include "a1i.mm";
include "mpd.mm";

theorem mpi(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume mpi.1: |- "ps";
  assume mpi.2: |- "( ph -> ( ps -> ch ) )";





  do {
    wph;
    wps;
    wch;
    wps;
    wph;
    mpi.1;
    a1i;
    mpi.2;
    mpd;
  };

  return '|-' "( ph -> ch )";
}
