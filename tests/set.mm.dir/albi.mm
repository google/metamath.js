include "wb.mm";
include "wal.mm";
include "biimp.mm";
include "al2imi.mm";
include "biimpr.mm";
include "impbid.mm";

theorem albi(wph: 'wff' ph, wps: 'wff' ps, vx: 'setvar' x) {





  do {
    wph;
    wps;
    wb;
    #;
    vx;
    wal;
    wph;
    vx;
    wal;
    wps;
    vx;
    wal;
    @0;
    wph;
    wps;
    vx;
    wph;
    wps;
    biimp;
    al2imi;
    @0;
    wps;
    wph;
    vx;
    wph;
    wps;
    biimpr;
    al2imi;
    impbid;
  };

  return '|-' "( A. x ( ph <-> ps ) -> ( A. x ph <-> A. x ps ) )";
}
