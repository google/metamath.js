include "wf.mm";
include "wa.mm";
include "wn.mm";
include "wo.mm";
include "comm0.mm";
include "df-c2.mm";
include "bi1.mm";
include "wdf-c1.mm";

theorem wcom0(wva: $term$ a) {





  do {
    wva;
    wf;
    wva;
    wva;
    wf;
    wa;
    wva;
    wf;
    wn;
    wa;
    wo;
    wva;
    wf;
    wva;
    comm0;
    df-c2;
    bi1;
    wdf-c1;
  };

  return $|- C ( a , 0 ) = 1$;
}
