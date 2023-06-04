include "kct.mm";
include "jca.mm";
include "syl.mm";

theorem syl2anc(ta: 'term' A, tr: 'term' R, ts: 'term' S, tt: 'term' T) {
  assume syl2anc.1: |- "R |= S";
  assume syl2anc.2: |- "R |= T";
  assume syl2anc.3: |- "( S , T ) |= A";





  do {
    tr;
    ts;
    tt;
    kct;
    ta;
    tr;
    ts;
    tt;
    syl2anc.1;
    syl2anc.2;
    jca;
    syl2anc.3;
    syl;
  };

  return '|-' "R |= A";
}
