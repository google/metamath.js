include "wb.mm";
include "biimpr.mm";
include "biimp.mm";
include "impbid.mm";

theorem bicom1(wph: $wff$ ph, wps: $wff$ ps) {





  do {
    wph;
    wps;
    wb;
    wps;
    wph;
    wph;
    wps;
    biimpr;
    wph;
    wps;
    biimp;
    impbid;
  };

  return $|-$ $( ( ph <-> ps ) -> ( ps <-> ph ) )$;
}
