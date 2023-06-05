include "wn.mm";
include "wi.mm";
include "a1i.mm";
include "mt3d.mm";

theorem nsyl2(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume nsyl2.1: |- "( ph -> -. ps )";
  assume nsyl2.2: |- "( -. ch -> ps )";





  do {
    wph;
    wch;
    wps;
    nsyl2.1;
    wch;
    wn;
    wps;
    wi;
    wph;
    nsyl2.2;
    a1i;
    mt3d;
  };

  return |- "( ph -> ch )";
}
