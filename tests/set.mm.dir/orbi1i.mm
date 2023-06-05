include "wo.mm";
include "orcom.mm";
include "orbi2i.mm";
include "3bitri.mm";

theorem orbi1i(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume orbi2i.1: |- "( ph <-> ps )";





  do {
    wph;
    wch;
    wo;
    wch;
    wph;
    wo;
    wch;
    wps;
    wo;
    wps;
    wch;
    wo;
    wph;
    wch;
    orcom;
    wph;
    wps;
    wch;
    orbi2i.1;
    orbi2i;
    wch;
    wps;
    orcom;
    3bitri;
  };

  return |- "( ( ph \\/ ch ) <-> ( ps \\/ ch ) )";
}
