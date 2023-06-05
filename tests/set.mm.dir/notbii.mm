include "wb.mm";
include "wn.mm";
include "notbi.mm";
include "mpbi.mm";

theorem notbii(wph: wff ph, wps: wff ps) {
  assume notbii.1: |- "( ph <-> ps )";





  do {
    wph;
    wps;
    wb;
    wph;
    wn;
    wps;
    wn;
    wb;
    notbii.1;
    wph;
    wps;
    notbi;
    mpbi;
  };

  return |- "( -. ph <-> -. ps )";
}
