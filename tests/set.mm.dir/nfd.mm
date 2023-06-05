include "wex.mm";
include "wal.mm";
include "wi.mm";
include "wnf.mm";
include "df-nf.mm";
include "sylibr.mm";

theorem nfd(wph: wff ph, wps: wff ps, vx: setvar x) {
  assume nfd.1: |- "( ph -> ( E. x ps -> A. x ps ) )";





  do {
    wph;
    wps;
    vx;
    wex;
    wps;
    vx;
    wal;
    wi;
    wps;
    vx;
    wnf;
    nfd.1;
    wps;
    vx;
    df-nf;
    sylibr;
  };

  return |- "( ph -> F/ x ps )";
}
