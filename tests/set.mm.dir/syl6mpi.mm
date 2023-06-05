include "mpi.mm";
include "syl6.mm";

theorem syl6mpi(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th, wta: wff ta) {
  assume syl6mpi.1: |- "( ph -> ( ps -> ch ) )";
  assume syl6mpi.2: |- "th";
  assume syl6mpi.3: |- "( ch -> ( th -> ta ) )";





  do {
    wph;
    wps;
    wch;
    wta;
    syl6mpi.1;
    wch;
    wth;
    wta;
    syl6mpi.2;
    syl6mpi.3;
    mpi;
    syl6;
  };

  return |- "( ph -> ( ps -> ta ) )";
}
