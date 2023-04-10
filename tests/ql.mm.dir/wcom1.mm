include "wt.mm";
include "wa.mm";
include "wn.mm";
include "wo.mm";
include "comm1.mm";
include "df-c2.mm";
include "bi1.mm";
include "wdf-c1.mm";

theorem wcom1(wva: $term$ a) {





  do {
    wt;
    wva;
    wt;
    wt;
    wva;
    wa;
    wt;
    wva;
    wn;
    wa;
    wo;
    wt;
    wva;
    wva;
    comm1;
    df-c2;
    bi1;
    wdf-c1;
  };

  return $|- C ( 1 , a ) = 1$;
}
