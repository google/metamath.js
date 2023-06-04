include "ax-cb1.mm";
include "id.mm";
include "syl2anc.mm";

theorem mpdan(tr: term R, ts: term S, tt: term T) {
  assume mpdan.1: |- "R |= S";
  assume mpdan.2: |- "( R , S ) |= T";





  do {
    tt;
    tr;
    tr;
    ts;
    tr;
    ts;
    tr;
    mpdan.1;
    ax-cb1;
    id;
    mpdan.1;
    mpdan.2;
    syl2anc;
  };

  return '|-' "R |= T";
}
