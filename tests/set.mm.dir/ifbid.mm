include "wb.mm";
include "cif.mm";
include "wceq.mm";
include "ifbi.mm";
include "syl.mm";

theorem ifbid(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, cA: $class$ A, cB: $class$ B) {
  assume ifbid.1: $|- ( ph -> ( ps <-> ch ) )$;





  do {
    wph;
    wps;
    wch;
    wb;
    wps;
    cA;
    cB;
    cif;
    wch;
    cA;
    cB;
    cif;
    wceq;
    ifbid.1;
    wps;
    wch;
    cA;
    cB;
    ifbi;
    syl;
  };

  return $|-$ $( ph -> if ( ps , A , B ) = if ( ch , A , B ) )$;
}
