include "wb.mm";
include "bicom.mm";
include "bibi2i.mm";
include "3bitri.mm";

theorem bibi1i(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume bibi2i.1: $|- ( ph <-> ps )$;





  do {
    wph;
    wch;
    wb;
    wch;
    wph;
    wb;
    wch;
    wps;
    wb;
    wps;
    wch;
    wb;
    wph;
    wch;
    bicom;
    wph;
    wps;
    wch;
    bibi2i.1;
    bibi2i;
    wch;
    wps;
    bicom;
    3bitri;
  };

  return $|-$ $( ( ph <-> ch ) <-> ( ps <-> ch ) )$;
}
