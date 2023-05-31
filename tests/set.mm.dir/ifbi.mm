include "wb.mm";
include "wa.mm";
include "wn.mm";
include "wo.mm";
include "cif.mm";
include "wceq.mm";
include "dfbi3.mm";
include "iftrue.mm";
include "eqcomd.mm";
include "sylan9eq.mm";
include "iffalse.mm";
include "jaoi.mm";
include "sylbi.mm";

theorem ifbi(wph: $wff$ ph, wps: $wff$ ps, cA: $class$ A, cB: $class$ B) {





  do {
    wph;
    wps;
    wb;
    wph;
    wps;
    wa;
    #;
    wph;
    wn;
    #;
    wps;
    wn;
    #;
    wa;
    #;
    wo;
    wph;
    cA;
    cB;
    cif;
    #;
    wps;
    cA;
    cB;
    cif;
    #;
    wceq;
    #;
    wph;
    wps;
    dfbi3;
    @0;
    @6;
    @3;
    wph;
    wps;
    @4;
    cA;
    @5;
    wph;
    cA;
    cB;
    iftrue;
    wps;
    @5;
    cA;
    wps;
    cA;
    cB;
    iftrue;
    eqcomd;
    sylan9eq;
    @1;
    @2;
    @4;
    cB;
    @5;
    wph;
    cA;
    cB;
    iffalse;
    @2;
    @5;
    cB;
    wps;
    cA;
    cB;
    iffalse;
    eqcomd;
    sylan9eq;
    jaoi;
    sylbi;
  };

  return $|-$ $( ( ph <-> ps ) -> if ( ph , A , B ) = if ( ps , A , B ) )$;
}
