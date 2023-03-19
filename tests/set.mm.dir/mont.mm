include "wtru.mm"
include "wmo.mm"
include "wex.mm"
include "weu.mm"
include "wi.mm"
include "wn.mm"
include "extt.mm"
include "unnt.mm"
include "mth8.mm"
include "mp2.mm"
include "df-mo.mm"
include "mtbir.mm"

theorem mont
  let vx: setvar x


  assert |- -. E* x T.

  proof
    wtru
    vx
    wmo
    wtru
    vx
    wex
    #
    wtru
    vx
    weu
    #
    wi
    #
    @0
    @1
    wn
    @2
    wn
    vx
    extt
    vx
    unnt
    @0
    @1
    mth8
    mp2
    wtru
    vx
    df-mo
    mtbir
end
