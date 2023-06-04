include "ax-simpr.mm";

theorem simpr(tr: 'term' R, ts: 'term' S) {
  assume ax-simpl.1: |- "R : bool";
  assume ax-simpl.2: |- "S : bool";





  do {
    tr;
    ts;
    ax-simpl.1;
    ax-simpl.2;
    ax-simpr;
  };

  return '|-' "( R , S ) |= S";
}
