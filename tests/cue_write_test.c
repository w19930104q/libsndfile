/*
** Copyright (C) 2026 Erik de Castro Lopo <erikd@mega-nerd.com>
**
** This program is free software; you can redistribute it and/or modify
** it under the terms of the GNU General Public License as published by
** the Free Software Foundation; either version 2 of the License, or
** (at your option) any later version.
**
** This program is distributed in the hope that it will be useful,
** but WITHOUT ANY WARRANTY; without even the implied warranty of
** MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
** GNU General Public License for more details.
**
** You should have received a copy of the GNU General Public License
** along with this program; if not, write to the Free Software
** Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
*/

/*
** Test writing cue points to newly created WAV (cue + LIST/adtl/labl chunks)
** and AIFF (MARK chunk) files. Cue indices, sample positions and names are
** read back and compared item by item. The written files are also parsed
** chunk by chunk, independently of the library, to verify that the chunk
** layout (field offsets, chunk sizes, padding) is correct.
*/

#include "sfconfig.h"

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#if HAVE_UNISTD_H
#include <unistd.h>
#else
#include "sf_unistd.h"
#endif

#include <sndfile.h>

#include "utils.h"

#define FRAME_COUNT		4096
#define CHANNEL_COUNT	2

#define SF_CUES_SIZE(count)	(sizeof (uint32_t) + sizeof (SF_CUE_POINT) * (count))

/* AIFF MARK pascal strings are stored with an odd length byte capped at 253. */
#define AIFF_NAME_MAX	253

static void	cue_roundtrip_test	(const char *filename, int filetype, int cue_count) ;
static void	cue_edge_name_test	(const char *filename, int filetype) ;
static void	cue_long_name_test	(const char *filename, int filetype) ;
static void	cue_replace_test	(const char *filename, int filetype) ;
static void	no_cue_test			(const char *filename, int filetype) ;

static uint16_t
get_le16 (const uint8_t *p)
{	return (uint16_t) (p [0] | (p [1] << 8)) ;
}

static uint32_t
get_le32 (const uint8_t *p)
{	return p [0] | (p [1] << 8) | (((uint32_t) p [2]) << 16) | (((uint32_t) p [3]) << 24) ;
}

static uint16_t
get_be16 (const uint8_t *p)
{	return (uint16_t) ((p [0] << 8) | p [1]) ;
}

static uint32_t
get_be32 (const uint8_t *p)
{	return (((uint32_t) p [0]) << 24) | (((uint32_t) p [1]) << 16) | (p [2] << 8) | p [3] ;
}

static uint8_t *
read_file (const char *filename, size_t *length)
{	FILE *f ;
	uint8_t *buf ;
	long size ;

	if ((f = fopen (filename, "rb")) == NULL)
	{	printf ("\n\nLine %d : cannot open '%s' for binary read.\n\n", __LINE__, filename) ;
		exit (1) ;
		} ;
	fseek (f, 0, SEEK_END) ;
	size = ftell (f) ;
	fseek (f, 0, SEEK_SET) ;
	if ((buf = malloc (size)) == NULL)
	{	printf ("\n\nLine %d : malloc failed.\n\n", __LINE__) ;
		exit (1) ;
		} ;
	if (fread (buf, 1, size, f) != (size_t) size)
	{	printf ("\n\nLine %d : short read on '%s'.\n\n", __LINE__, filename) ;
		exit (1) ;
		} ;
	fclose (f) ;
	*length = (size_t) size ;
	return buf ;
}

static void
gen_audio (short *data, int frames, int channels)
{	int k ;
	for (k = 0 ; k < frames * channels ; k++)
		data [k] = (short) (((uint32_t) k * 2654435761u) >> 16) ;
}

static void
fill_cues (SF_CUES *cues, int cue_count)
{	int k ;
	cues->cue_count = (uint32_t) cue_count ;
	for (k = 0 ; k < cue_count ; k++)
	{	cues->cue_points [k].indx = k + 1 ;
		cues->cue_points [k].position = 97 * k + 13 ;
		cues->cue_points [k].fcc_chunk = 0x61746164 ; /* 'data' */
		cues->cue_points [k].chunk_start = 0 ;
		cues->cue_points [k].block_start = 0 ;
		cues->cue_points [k].sample_offset = 97 * k + 13 ;
		snprintf (cues->cue_points [k].name, sizeof (cues->cue_points [k].name), "cue-%d", k + 1) ;
		} ;
}

static void
write_file_with_cues (const char *filename, int filetype, const SF_CUES *cues, size_t cues_size,
						const short *audio, int frames)
{	SF_INFO sfinfo ;
	SNDFILE *file ;

	memset (&sfinfo, 0, sizeof (sfinfo)) ;
	sfinfo.samplerate = 44100 ;
	sfinfo.channels = CHANNEL_COUNT ;
	sfinfo.format = filetype ;

	file = test_open_file_or_die (filename, SFM_WRITE, &sfinfo, SF_TRUE, __LINE__) ;

	if (cues != NULL && sf_command (file, SFC_SET_CUE, (void *) cues, (int) cues_size) == SF_FALSE)
	{	printf ("\n\nLine %d : sf_command (SFC_SET_CUE) failed : %s\n\n", __LINE__, sf_strerror (file)) ;
		exit (1) ;
		} ;

	test_write_short_or_die (file, 0, audio, frames * CHANNEL_COUNT, __LINE__) ;
	sf_close (file) ;
}

/* Expected name after an AIFF write/read round trip. */
static void
aiff_expected_name (char *dst, size_t dstlen, const char *src)
{	size_t len = strlen (src) ;
	if (len > AIFF_NAME_MAX)
		len = AIFF_NAME_MAX ;
	if (len >= dstlen)
		len = dstlen - 1 ;
	memcpy (dst, src, len) ;
	dst [len] = 0 ;
}

static void
read_and_compare_cues (const char *filename, int filetype, const SF_CUES *write_cues, int cue_count, int line)
{	SF_CUES *read_cues ;
	SF_INFO sfinfo ;
	SNDFILE *file ;
	uint32_t count = 0 ;
	size_t cues_size = SF_CUES_SIZE (cue_count) ;
	int is_aiff = (filetype & SF_FORMAT_TYPEMASK) == SF_FORMAT_AIFF ;
	int k ;

	memset (&sfinfo, 0, sizeof (sfinfo)) ;
	file = test_open_file_or_die (filename, SFM_READ, &sfinfo, SF_TRUE, line) ;

	if (sf_command (file, SFC_GET_CUE_COUNT, &count, sizeof (count)) == SF_FALSE)
	{	printf ("\n\nLine %d : SFC_GET_CUE_COUNT failed on '%s'.\n\n", line, filename) ;
		exit (1) ;
		} ;
	if ((int) count != cue_count)
	{	printf ("\n\nLine %d : cue count %d, expected %d.\n\n", line, (int) count, cue_count) ;
		exit (1) ;
		} ;

	if ((read_cues = calloc (1, cues_size)) == NULL)
	{	printf ("\n\nLine %d : calloc failed.\n\n", line) ;
		exit (1) ;
		} ;
	if (sf_command (file, SFC_GET_CUE, read_cues, (int) cues_size) == SF_FALSE)
	{	printf ("\n\nLine %d : SFC_GET_CUE failed on '%s'.\n\n", line, filename) ;
		exit (1) ;
		} ;
	sf_close (file) ;

	for (k = 0 ; k < cue_count ; k++)
	{	const SF_CUE_POINT *w = &write_cues->cue_points [k] ;
		const SF_CUE_POINT *r = &read_cues->cue_points [k] ;
		char expected_name [256] ;

		if (r->indx != w->indx)
		{	printf ("\n\nLine %d : cue %d indx %d, expected %d.\n\n", line, k, r->indx, w->indx) ;
			exit (1) ;
			} ;
		if (r->position != w->position)
		{	printf ("\n\nLine %d : cue %d position %u, expected %u.\n\n", line, k, r->position, w->position) ;
			exit (1) ;
			} ;
		if (r->sample_offset != w->sample_offset)
		{	printf ("\n\nLine %d : cue %d sample_offset %u, expected %u.\n\n", line, k, r->sample_offset, w->sample_offset) ;
			exit (1) ;
			} ;

		if (is_aiff)
			aiff_expected_name (expected_name, sizeof (expected_name), w->name) ;
		else
		{	snprintf (expected_name, sizeof (expected_name), "%s", w->name) ;
			} ;
		if (strcmp (r->name, expected_name) != 0)
		{	printf ("\n\nLine %d : cue %d name '%s', expected '%s'.\n\n", line, k, r->name, expected_name) ;
			exit (1) ;
			} ;
		} ;

	free (read_cues) ;
}

static void
read_and_compare_audio (const char *filename, const short *audio, int frames, int line)
{	SF_INFO sfinfo ;
	SNDFILE *file ;
	short *readback ;
	sf_count_t got ;

	memset (&sfinfo, 0, sizeof (sfinfo)) ;
	file = test_open_file_or_die (filename, SFM_READ, &sfinfo, SF_TRUE, line) ;

	if ((readback = malloc (frames * CHANNEL_COUNT * sizeof (short))) == NULL)
	{	printf ("\n\nLine %d : malloc failed.\n\n", line) ;
		exit (1) ;
		} ;
	got = sf_readf_short (file, readback, frames) ;
	sf_close (file) ;

	if (got != frames)
	{	printf ("\n\nLine %d : read %lld frames, expected %d.\n\n", line, (long long) got, frames) ;
		exit (1) ;
		} ;
	if (memcmp (readback, audio, frames * CHANNEL_COUNT * sizeof (short)) != 0)
	{	printf ("\n\nLine %d : audio data mismatch, not bit-exact.\n\n", line) ;
		exit (1) ;
		} ;
	free (readback) ;
}

/*------------------------------------------------------------------------------
** Independent chunk-by-chunk verification of a WAV file containing a 'cue '
** chunk and, if any cue has a non-empty name, a LIST/adtl chunk of 'labl'
** subchunks.
*/

static void
verify_wav_chunks (const char *filename, const SF_CUES *cues, int cue_count, int line)
{	uint8_t *buf ;
	size_t length, offset, riff_size ;
	int found_cue = 0, found_labl_list = 0 ;
	int named_cues = 0, k ;

	buf = read_file (filename, &length) ;

	if (length < 12 || memcmp (buf, "RIFF", 4) != 0 || memcmp (buf + 8, "WAVE", 4) != 0)
	{	printf ("\n\nLine %d : '%s' is not a RIFF/WAVE file.\n\n", line, filename) ;
		exit (1) ;
		} ;
	riff_size = get_le32 (buf + 4) ;
	if (riff_size != length - 8)
	{	printf ("\n\nLine %d : RIFF size %zu, expected %zu.\n\n", line, riff_size, length - 8) ;
		exit (1) ;
		} ;

	for (k = 0 ; k < cue_count ; k++)
		if (cues->cue_points [k].name [0] != 0)
			named_cues ++ ;

	offset = 12 ;
	while (offset + 8 <= length)
	{	const uint8_t *chunk = buf + offset ;
		uint32_t chunk_size = get_le32 (chunk + 4) ;

		if (offset + 8 + chunk_size > length)
		{	printf ("\n\nLine %d : chunk '%.4s' at %zu overruns file (size %u).\n\n",
					line, chunk, offset, chunk_size) ;
			exit (1) ;
			} ;

		if (memcmp (chunk, "cue ", 4) == 0)
		{	const uint8_t *rec ;
			if (found_cue)
			{	printf ("\n\nLine %d : multiple 'cue ' chunks.\n\n", line) ;
				exit (1) ;
				} ;
			found_cue = 1 ;
			if (chunk_size != 4 + (uint32_t) cue_count * 24)
			{	printf ("\n\nLine %d : 'cue ' chunk size %u, expected %d.\n\n", line, chunk_size, 4 + cue_count * 24) ;
				exit (1) ;
				} ;
			if (get_le32 (chunk + 8) != (uint32_t) cue_count)
			{	printf ("\n\nLine %d : 'cue ' count %u, expected %d.\n\n", line, get_le32 (chunk + 8), cue_count) ;
				exit (1) ;
				} ;
			rec = chunk + 12 ;
			for (k = 0 ; k < cue_count ; k++, rec += 24)
			{	const SF_CUE_POINT *cp = &cues->cue_points [k] ;
				if ((int32_t) get_le32 (rec) != cp->indx ||
					get_le32 (rec + 4) != cp->position ||
					memcmp (rec + 8, "data", 4) != 0 ||
					get_le32 (rec + 12) != 0 || get_le32 (rec + 16) != 0 ||
					get_le32 (rec + 20) != cp->sample_offset)
				{	printf ("\n\nLine %d : 'cue ' record %d fields wrong "
							"(id %u pos %u '%.4s' %u %u offset %u).\n\n", line, k,
							get_le32 (rec), get_le32 (rec + 4), rec + 8,
							get_le32 (rec + 12), get_le32 (rec + 16), get_le32 (rec + 20)) ;
					exit (1) ;
					} ;
				} ;
			}
		else if (memcmp (chunk, "LIST", 4) == 0 && chunk_size >= 4 && memcmp (chunk + 8, "adtl", 4) == 0)
		{	size_t sub = offset + 12, end = offset + 8 + chunk_size ;
			int labl_count = 0 ;

			found_labl_list = 1 ;
			while (sub + 8 <= end)
			{	const uint8_t *sc = buf + sub ;
				uint32_t sc_size = get_le32 (sc + 4) ;
				size_t namelen ;

				if (sub + 8 + sc_size > end)
				{	printf ("\n\nLine %d : adtl subchunk at %zu overruns LIST.\n\n", line, sub) ;
					exit (1) ;
					} ;
				if (memcmp (sc, "labl", 4) != 0)
				{	printf ("\n\nLine %d : unexpected adtl subchunk '%.4s'.\n\n", line, sc) ;
					exit (1) ;
					} ;

				/* Find the cue this label belongs to. */
				for (k = 0 ; k < cue_count ; k++)
					if ((int32_t) get_le32 (sc + 8) == cues->cue_points [k].indx)
						break ;
				if (k == cue_count)
				{	printf ("\n\nLine %d : 'labl' for unknown cue id %u.\n\n", line, get_le32 (sc + 8)) ;
					exit (1) ;
					} ;

				namelen = strlen (cues->cue_points [k].name) ;
				if (sc_size != 4 + namelen + 1)
				{	printf ("\n\nLine %d : 'labl' size %u, expected %zu (4 + name %zu + NUL).\n\n",
							line, sc_size, 4 + namelen + 1, namelen) ;
					exit (1) ;
					} ;
				if (memcmp (sc + 12, cues->cue_points [k].name, namelen) != 0 || sc [12 + namelen] != 0)
				{	printf ("\n\nLine %d : 'labl' text mismatch for cue %d.\n\n", line, k) ;
					exit (1) ;
					} ;

				labl_count ++ ;
				sub += 8 + sc_size + (sc_size & 1) ;
				} ;

			if (sub != end)
			{	printf ("\n\nLine %d : LIST/adtl subchunks end at %zu, chunk ends at %zu.\n\n", line, sub, end) ;
				exit (1) ;
				} ;
			if (labl_count != named_cues)
			{	printf ("\n\nLine %d : found %d 'labl' subchunks, expected %d.\n\n", line, labl_count, named_cues) ;
				exit (1) ;
				} ;
			} ;

		offset += 8 + chunk_size + (chunk_size & 1) ;
		} ;

	if (offset != length)
	{	printf ("\n\nLine %d : chunks end at %zu but file length is %zu.\n\n", line, offset, length) ;
		exit (1) ;
		} ;

	if (cue_count > 0 && ! found_cue)
	{	printf ("\n\nLine %d : no 'cue ' chunk found in '%s'.\n\n", line, filename) ;
		exit (1) ;
		} ;
	if (named_cues > 0 && ! found_labl_list)
	{	printf ("\n\nLine %d : no LIST/adtl chunk found in '%s'.\n\n", line, filename) ;
		exit (1) ;
		} ;
	if (named_cues == 0 && found_labl_list)
	{	printf ("\n\nLine %d : unexpected LIST/adtl chunk in '%s'.\n\n", line, filename) ;
		exit (1) ;
		} ;

	free (buf) ;
}

/*------------------------------------------------------------------------------
** Independent chunk-by-chunk verification of an AIFF file containing a MARK
** chunk.
*/

static void
verify_aiff_chunks (const char *filename, const SF_CUES *cues, int cue_count, int line)
{	uint8_t *buf ;
	size_t length, offset, form_size ;
	int found_mark = 0, k ;

	buf = read_file (filename, &length) ;

	if (length < 12 || memcmp (buf, "FORM", 4) != 0 ||
		(memcmp (buf + 8, "AIFF", 4) != 0 && memcmp (buf + 8, "AIFC", 4) != 0))
	{	printf ("\n\nLine %d : '%s' is not a FORM/AIFF file.\n\n", line, filename) ;
		exit (1) ;
		} ;
	form_size = get_be32 (buf + 4) ;
	if (form_size != length - 8)
	{	printf ("\n\nLine %d : FORM size %zu, expected %zu.\n\n", line, form_size, length - 8) ;
		exit (1) ;
		} ;

	offset = 12 ;
	while (offset + 8 <= length)
	{	const uint8_t *chunk = buf + offset ;
		uint32_t chunk_size = get_be32 (chunk + 4) ;

		if (offset + 8 + chunk_size > length)
		{	printf ("\n\nLine %d : chunk '%.4s' at %zu overruns file (size %u).\n\n",
					line, chunk, offset, chunk_size) ;
			exit (1) ;
			} ;

		if (memcmp (chunk, "MARK", 4) == 0)
		{	const uint8_t *rec = chunk + 10 ;
			const uint8_t *end = chunk + 8 + chunk_size ;
			uint32_t expected_size = 2 ;

			if (found_mark)
			{	printf ("\n\nLine %d : multiple MARK chunks.\n\n", line) ;
				exit (1) ;
				} ;
			found_mark = 1 ;

			if (get_be16 (chunk + 8) != (uint32_t) cue_count)
			{	printf ("\n\nLine %d : MARK count %u, expected %d.\n\n", line, get_be16 (chunk + 8), cue_count) ;
				exit (1) ;
				} ;

			for (k = 0 ; k < cue_count ; k++)
			{	const SF_CUE_POINT *cp = &cues->cue_points [k] ;
				char expected [256] ;
				size_t expect_len, stored_len ;

				if (rec + 7 > end)
				{	printf ("\n\nLine %d : MARK record %d overruns chunk.\n\n", line, k) ;
					exit (1) ;
					} ;
				if ((int32_t) get_be16 (rec) != cp->indx)
				{	printf ("\n\nLine %d : MARK record %d id %u, expected %d.\n\n", line, k, get_be16 (rec), cp->indx) ;
					exit (1) ;
					} ;
				if (get_be32 (rec + 2) != cp->sample_offset)
				{	printf ("\n\nLine %d : MARK record %d position %u, expected %u (sample frames).\n\n",
							line, k, get_be32 (rec + 2), cp->sample_offset) ;
					exit (1) ;
					} ;

				aiff_expected_name (expected, sizeof (expected), cp->name) ;
				expect_len = strlen (expected) ;
				/* The stored pascal string length is always odd : even length
				** names have their trailing NUL counted instead. */
				stored_len = (expect_len & 1) ? expect_len : expect_len + 1 ;

				if (rec [6] != stored_len)
				{	printf ("\n\nLine %d : MARK record %d pstring length %u, expected %zu.\n\n",
							line, k, rec [6], stored_len) ;
					exit (1) ;
					} ;
				if (rec + 7 + stored_len > end)
				{	printf ("\n\nLine %d : MARK record %d pstring overruns chunk.\n\n", line, k) ;
					exit (1) ;
					} ;
				if (memcmp (rec + 7, expected, expect_len) != 0)
				{	printf ("\n\nLine %d : MARK record %d name mismatch.\n\n", line, k) ;
					exit (1) ;
					} ;

				expected_size += 6 + 1 + (uint32_t) stored_len ;
				rec += 6 + 1 + stored_len ;
				} ;

			if (chunk_size != expected_size)
			{	printf ("\n\nLine %d : MARK chunk size %u, expected %u.\n\n", line, chunk_size, expected_size) ;
				exit (1) ;
				} ;
			if (rec != end)
			{	printf ("\n\nLine %d : MARK records end at %p, chunk ends at %p.\n\n", line, (void *) rec, (void *) end) ;
				exit (1) ;
				} ;
			} ;

		offset += 8 + chunk_size + (chunk_size & 1) ;
		} ;

	if (offset != length)
	{	printf ("\n\nLine %d : chunks end at %zu but file length is %zu.\n\n", line, offset, length) ;
		exit (1) ;
		} ;

	if (cue_count > 0 && ! found_mark)
	{	printf ("\n\nLine %d : no MARK chunk found in '%s'.\n\n", line, filename) ;
		exit (1) ;
		} ;

	free (buf) ;
}

static void
verify_chunks (const char *filename, int filetype, const SF_CUES *cues, int cue_count, int line)
{	if ((filetype & SF_FORMAT_TYPEMASK) == SF_FORMAT_AIFF)
		verify_aiff_chunks (filename, cues, cue_count, line) ;
	else
		verify_wav_chunks (filename, cues, cue_count, line) ;
}

/*----------------------------------------------------------------------------*/

static void
cue_roundtrip_test (const char *filename, int filetype, int cue_count)
{	SF_CUES *cues ;
	short *audio ;
	size_t cues_size = SF_CUES_SIZE (cue_count) ;

	print_test_name ("cue_roundtrip_test", filename) ;

	cues = calloc (1, cues_size) ;
	audio = malloc (FRAME_COUNT * CHANNEL_COUNT * sizeof (short)) ;
	if (cues == NULL || audio == NULL)
	{	printf ("\n\nLine %d : malloc failed.\n\n", __LINE__) ;
		exit (1) ;
		} ;

	fill_cues (cues, cue_count) ;
	gen_audio (audio, FRAME_COUNT, CHANNEL_COUNT) ;

	write_file_with_cues (filename, filetype, cues, cues_size, audio, FRAME_COUNT) ;
	read_and_compare_cues (filename, filetype, cues, cue_count, __LINE__) ;
	read_and_compare_audio (filename, audio, FRAME_COUNT, __LINE__) ;
	verify_chunks (filename, filetype, cues, cue_count, __LINE__) ;

	free (cues) ;
	free (audio) ;
	unlink (filename) ;
	puts ("ok") ;
}

static void
cue_edge_name_test (const char *filename, int filetype)
{	/* Empty name, and names needing zero or one pad byte in both the
	** WAV 'labl' subchunk and the AIFF pascal string. */
	static const char *names [] = { "", "a", "ab", "abc", "abcd" } ;
	SF_CUES_VAR (5) cues ;
	short *audio ;
	int k ;

	print_test_name ("cue_edge_name_test", filename) ;

	memset (&cues, 0, sizeof (cues)) ;
	cues.cue_count = ARRAY_LEN (names) ;
	for (k = 0 ; k < (int) ARRAY_LEN (names) ; k++)
	{	cues.cue_points [k].indx = 21 + k ;
		cues.cue_points [k].position = 500 * k ;
		cues.cue_points [k].fcc_chunk = 0x61746164 ;
		cues.cue_points [k].sample_offset = 500 * k ;
		snprintf (cues.cue_points [k].name, sizeof (cues.cue_points [k].name), "%s", names [k]) ;
		} ;

	audio = malloc (FRAME_COUNT * CHANNEL_COUNT * sizeof (short)) ;
	if (audio == NULL)
	{	printf ("\n\nLine %d : malloc failed.\n\n", __LINE__) ;
		exit (1) ;
		} ;
	gen_audio (audio, FRAME_COUNT, CHANNEL_COUNT) ;

	write_file_with_cues (filename, filetype, (const SF_CUES *) &cues, sizeof (cues), audio, FRAME_COUNT) ;
	read_and_compare_cues (filename, filetype, (const SF_CUES *) &cues, cues.cue_count, __LINE__) ;
	read_and_compare_audio (filename, audio, FRAME_COUNT, __LINE__) ;
	verify_chunks (filename, filetype, (const SF_CUES *) &cues, cues.cue_count, __LINE__) ;

	free (audio) ;
	unlink (filename) ;
	puts ("ok") ;
}

static void
cue_long_name_test (const char *filename, int filetype)
{	/* Names of 255 and 254 characters : the largest names that fit the
	** SF_CUE_POINT name field. WAV stores them whole (the 254 character
	** name needs a pad byte in its 'labl' subchunk), AIFF truncates to
	** the largest odd pascal string length of 253. */
	SF_CUES_VAR (2) cues ;
	short *audio ;
	int k ;

	print_test_name ("cue_long_name_test", filename) ;

	memset (&cues, 0, sizeof (cues)) ;
	cues.cue_count = 2 ;
	for (k = 0 ; k < 2 ; k++)
	{	int namelen = 255 - k ;
		cues.cue_points [k].indx = 7 + k ;
		cues.cue_points [k].position = 1234 * k ;
		cues.cue_points [k].fcc_chunk = 0x61746164 ;
		cues.cue_points [k].sample_offset = 1234 * k ;
		memset (cues.cue_points [k].name, 'a' + k, namelen) ;
		cues.cue_points [k].name [namelen] = 0 ;
		} ;

	audio = malloc (FRAME_COUNT * CHANNEL_COUNT * sizeof (short)) ;
	if (audio == NULL)
	{	printf ("\n\nLine %d : malloc failed.\n\n", __LINE__) ;
		exit (1) ;
		} ;
	gen_audio (audio, FRAME_COUNT, CHANNEL_COUNT) ;

	write_file_with_cues (filename, filetype, (const SF_CUES *) &cues, sizeof (cues), audio, FRAME_COUNT) ;
	read_and_compare_cues (filename, filetype, (const SF_CUES *) &cues, cues.cue_count, __LINE__) ;
	read_and_compare_audio (filename, audio, FRAME_COUNT, __LINE__) ;
	verify_chunks (filename, filetype, (const SF_CUES *) &cues, cues.cue_count, __LINE__) ;

	free (audio) ;
	unlink (filename) ;
	puts ("ok") ;
}

static void
cue_replace_test (const char *filename, int filetype)
{	/* A second SFC_SET_CUE call must replace the cues set by the first. */
	SF_CUES_VAR (2) first ;
	SF_CUES_VAR (5) second ;
	short *audio ;
	int k ;

	print_test_name ("cue_replace_test", filename) ;

	memset (&first, 0, sizeof (first)) ;
	first.cue_count = 2 ;
	for (k = 0 ; k < 2 ; k++)
	{	first.cue_points [k].indx = k + 1 ;
		first.cue_points [k].position = 10 * k ;
		first.cue_points [k].fcc_chunk = 0x61746164 ;
		first.cue_points [k].sample_offset = 10 * k ;
		snprintf (first.cue_points [k].name, sizeof (first.cue_points [k].name), "first-%d", k) ;
		} ;

	memset (&second, 0, sizeof (second)) ;
	second.cue_count = 5 ;
	for (k = 0 ; k < 5 ; k++)
	{	second.cue_points [k].indx = 100 + k ;
		second.cue_points [k].position = 77 * k ;
		second.cue_points [k].fcc_chunk = 0x61746164 ;
		second.cue_points [k].sample_offset = 77 * k ;
		snprintf (second.cue_points [k].name, sizeof (second.cue_points [k].name), "second-%d", k) ;
		} ;

	audio = malloc (FRAME_COUNT * CHANNEL_COUNT * sizeof (short)) ;
	if (audio == NULL)
	{	printf ("\n\nLine %d : malloc failed.\n\n", __LINE__) ;
		exit (1) ;
		} ;
	gen_audio (audio, FRAME_COUNT, CHANNEL_COUNT) ;

	{	SF_INFO sfinfo ;
		SNDFILE *file ;

		memset (&sfinfo, 0, sizeof (sfinfo)) ;
		sfinfo.samplerate = 44100 ;
		sfinfo.channels = CHANNEL_COUNT ;
		sfinfo.format = filetype ;

		file = test_open_file_or_die (filename, SFM_WRITE, &sfinfo, SF_TRUE, __LINE__) ;
		if (sf_command (file, SFC_SET_CUE, &first, sizeof (first)) == SF_FALSE)
		{	printf ("\n\nLine %d : first SFC_SET_CUE failed.\n\n", __LINE__) ;
			exit (1) ;
			} ;
		if (sf_command (file, SFC_SET_CUE, &second, sizeof (second)) == SF_FALSE)
		{	printf ("\n\nLine %d : second SFC_SET_CUE failed.\n\n", __LINE__) ;
			exit (1) ;
			} ;
		test_write_short_or_die (file, 0, audio, FRAME_COUNT * CHANNEL_COUNT, __LINE__) ;
		sf_close (file) ;
		} ;

	read_and_compare_cues (filename, filetype, (const SF_CUES *) &second, second.cue_count, __LINE__) ;
	read_and_compare_audio (filename, audio, FRAME_COUNT, __LINE__) ;
	verify_chunks (filename, filetype, (const SF_CUES *) &second, second.cue_count, __LINE__) ;

	free (audio) ;
	unlink (filename) ;
	puts ("ok") ;
}

static void
no_cue_test (const char *filename, int filetype)
{	/* Files written without cues must behave as before : no cue count,
	** bit-exact audio. */
	SF_INFO sfinfo ;
	SNDFILE *file ;
	short *audio, *readback ;
	uint32_t count = 0 ;
	sf_count_t got ;

	print_test_name ("no_cue_test", filename) ;

	audio = malloc (FRAME_COUNT * CHANNEL_COUNT * sizeof (short)) ;
	readback = malloc (FRAME_COUNT * CHANNEL_COUNT * sizeof (short)) ;
	if (audio == NULL || readback == NULL)
	{	printf ("\n\nLine %d : malloc failed.\n\n", __LINE__) ;
		exit (1) ;
		} ;
	gen_audio (audio, FRAME_COUNT, CHANNEL_COUNT) ;

	write_file_with_cues (filename, filetype, NULL, 0, audio, FRAME_COUNT) ;

	memset (&sfinfo, 0, sizeof (sfinfo)) ;
	file = test_open_file_or_die (filename, SFM_READ, &sfinfo, SF_TRUE, __LINE__) ;
	if (sf_command (file, SFC_GET_CUE_COUNT, &count, sizeof (count)) != SF_FALSE)
	{	printf ("\n\nLine %d : SFC_GET_CUE_COUNT should fail on a file without cues (count %u).\n\n", __LINE__, count) ;
		exit (1) ;
		} ;
	got = sf_readf_short (file, readback, FRAME_COUNT) ;
	sf_close (file) ;

	if (got != FRAME_COUNT || memcmp (readback, audio, FRAME_COUNT * CHANNEL_COUNT * sizeof (short)) != 0)
	{	printf ("\n\nLine %d : audio data mismatch on file without cues.\n\n", __LINE__) ;
		exit (1) ;
		} ;

	free (audio) ;
	free (readback) ;
	unlink (filename) ;
	puts ("ok") ;
}

int
main (void)
{
	cue_roundtrip_test ("cue_write_2.wav", SF_FORMAT_WAV | SF_FORMAT_PCM_16, 2) ;
	cue_roundtrip_test ("cue_write_50.wav", SF_FORMAT_WAV | SF_FORMAT_PCM_16, 50) ;
	cue_roundtrip_test ("cue_write_2.aiff", SF_FORMAT_AIFF | SF_FORMAT_PCM_16, 2) ;
	cue_roundtrip_test ("cue_write_50.aiff", SF_FORMAT_AIFF | SF_FORMAT_PCM_16, 50) ;

	cue_edge_name_test ("cue_edge.wav", SF_FORMAT_WAV | SF_FORMAT_PCM_16) ;
	cue_edge_name_test ("cue_edge.aiff", SF_FORMAT_AIFF | SF_FORMAT_PCM_16) ;

	cue_long_name_test ("cue_long.wav", SF_FORMAT_WAV | SF_FORMAT_PCM_16) ;
	cue_long_name_test ("cue_long.aiff", SF_FORMAT_AIFF | SF_FORMAT_PCM_16) ;

	cue_replace_test ("cue_replace.wav", SF_FORMAT_WAV | SF_FORMAT_PCM_16) ;
	cue_replace_test ("cue_replace.aiff", SF_FORMAT_AIFF | SF_FORMAT_PCM_16) ;

	no_cue_test ("cue_none.wav", SF_FORMAT_WAV | SF_FORMAT_PCM_16) ;
	no_cue_test ("cue_none.aiff", SF_FORMAT_AIFF | SF_FORMAT_PCM_16) ;

	return 0 ;
}
