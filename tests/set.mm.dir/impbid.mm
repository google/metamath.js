include "wb.mm";
include "impbid21d.mm";
include "pm2.43i.mm";

theorem impbid(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume impbid.1: |- "( ph -> ( ps -> ch ) )";
  assume impbid.2: |- "( ph -> ( ch -> ps ) )";





  do {
    wph;
    wps;
    wch;
    wb;
    wph;
    wph;
    wps;
    wch;
    impbid.1;
    impbid.2;
    impbid21d;
    pm2.43i;
  };

  return |- "( ph -> ( ps <-> ch ) )";
}
