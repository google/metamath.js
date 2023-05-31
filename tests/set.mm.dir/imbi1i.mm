include "wb.mm";
include "wi.mm";
include "imbi1.mm";
include "ax-mp.mm";

theorem imbi1i(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume imbi1i.1: $|- ( ph <-> ps )$;





  do {
    wph;
    wps;
    wb;
    wph;
    wch;
    wi;
    wps;
    wch;
    wi;
    wb;
    imbi1i.1;
    wph;
    wps;
    wch;
    imbi1;
    ax-mp;
  };

  return $|-$ $( ( ph -> ch ) <-> ( ps -> ch ) )$;
}
