include "wtru.mm";
include "cv.mm";
include "wceq.mm";
include "wal.mm";
include "wi.mm";
include "id.mm";
include "df-tru.mm";
include "mpbir.mm";

theorem tru() {



  let vx.tru: setvar x;

  do {
    wtru;
    vx.tru;
    cv;
    #;
    @0;
    wceq;
    vx.tru;
    wal;
    #;
    @1;
    wi;
    @1;
    id;
    vx.tru;
    df-tru;
    mpbir;
  };

  return '|-' "T.";
}
