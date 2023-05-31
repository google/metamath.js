include "mpbiran.mm";
include "mpbir.mm";

theorem mpbir2an(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume mpbir2an.1: $|- ps$;
  assume mpbir2an.2: $|- ch$;
  assume mpbiran2an.1: $|- ( ph <-> ( ps /\ ch ) )$;





  do {
    wph;
    wch;
    mpbir2an.2;
    wph;
    wps;
    wch;
    mpbir2an.1;
    mpbiran2an.1;
    mpbiran;
    mpbir;
  };

  return $|-$ $ph$;
}
