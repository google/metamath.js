include "wa.mm";
include "jca.mm";
include "sylibr.mm";

theorem sylanbrc(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th) {
  assume sylanbrc.1: $|- ( ph -> ps )$;
  assume sylanbrc.2: $|- ( ph -> ch )$;
  assume sylanbrc.3: $|- ( th <-> ( ps /\ ch ) )$;





  do {
    wph;
    wps;
    wch;
    wa;
    wth;
    wph;
    wps;
    wch;
    sylanbrc.1;
    sylanbrc.2;
    jca;
    sylanbrc.3;
    sylibr;
  };

  return $|-$ $( ph -> th )$;
}
