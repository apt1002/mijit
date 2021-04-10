#!/bin/sh
set -e  # halt on error

FIX_OPTIONS=''
if [ "$FIX" = 1 ]; then
  FIX_OPTIONS='--fix -Z unstable-options --allow-staged'
fi

PEDANTIC_OPTIONS=''
if [ "$PEDANTIC" = 1 ]; then
  PEDANTIC_OPTIONS='-W clippy::pedantic'
fi

cargo clippy --color=always $FIX_OPTIONS -- $PEDANTIC_OPTIONS \
  -A clippy::unreadable_literal \
  -A clippy::redundant_field_names \
  -A clippy::missing_errors_doc \
  -A clippy::missing_panics_doc \
  -A clippy::cast_possible_truncation \
  -A clippy::cast_possible_wrap \
  -A clippy::cast_sign_loss \
  -A clippy::must_use_candidate \
  -A clippy::enum_glob_use \
  -A clippy::doc_markdown \
  "$@"
