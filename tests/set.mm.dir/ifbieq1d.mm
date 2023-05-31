include "cif.mm";
include "ifbid.mm";
include "ifeq1d.mm";
include "eqtrd.mm";

theorem ifbieq1d(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, cA: $class$ A, cB: $class$ B, cC: $class$ C) {
  assume ifbieq1d.1: $|- ( ph -> ( ps <-> ch ) )$;
  assume ifbieq1d.2: $|- ( ph -> A = B )$;





  do {
    wph;
    wps;
    cA;
    cC;
    cif;
    wch;
    cA;
    cC;
    cif;
    wch;
    cB;
    cC;
    cif;
    wph;
    wps;
    wch;
    cA;
    cC;
    ifbieq1d.1;
    ifbid;
    wph;
    wch;
    cA;
    cB;
    cC;
    ifbieq1d.2;
    ifeq1d;
    eqtrd;
  };

  return $|-$ $( ph -> if ( ps , A , C ) = if ( ch , B , C ) )$;
}
