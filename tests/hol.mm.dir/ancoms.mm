include "kct.mm";
include "ax-cb1.mm";
include "wctr.mm";
include "wctl.mm";
include "simpr.mm";
include "simpl.mm";
include "syl2anc.mm";

theorem ancoms(tr: 'term' R, ts: 'term' S, tt: 'term' T) {
  assume ancoms.1: |- "( R , S ) |= T";





  do {
    tt;
    ts;
    tr;
    kct;
    tr;
    ts;
    ts;
    tr;
    tr;
    ts;
    tt;
    tr;
    ts;
    kct;
    ancoms.1;
    ax-cb1;
    #;
    wctr;
    #;
    tr;
    ts;
    @0;
    wctl;
    #;
    simpr;
    ts;
    tr;
    @1;
    @2;
    simpl;
    ancoms.1;
    syl2anc;
  };

  return '|-' "( S , R ) |= T";
}
