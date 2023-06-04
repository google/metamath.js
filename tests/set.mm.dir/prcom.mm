include "csn.mm";
include "cun.mm";
include "cpr.mm";
include "uncom.mm";
include "df-pr.mm";
include "3eqtr4i.mm";

theorem prcom(cA: 'class' A, cB: 'class' B) {





  do {
    cA;
    csn;
    #;
    cB;
    csn;
    #;
    cun;
    @1;
    @0;
    cun;
    cA;
    cB;
    cpr;
    cB;
    cA;
    cpr;
    @0;
    @1;
    uncom;
    cA;
    cB;
    df-pr;
    cB;
    cA;
    df-pr;
    3eqtr4i;
  };

  return '|-' "{ A , B } = { B , A }";
}
