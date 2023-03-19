include "com.mm"
include "wcel.mm"
include "wlim.mm"
include "word.mm"
include "wn.mm"
include "nnord.mm"
include "ordirr.mm"
include "syl.mm"
include "cv.mm"
include "wi.mm"
include "wal.mm"
include "con0.mm"
include "elom.mm"
include "simprbi.mm"
include "wceq.mm"
include "limeq.mm"
include "eleq2.mm"
include "imbi12d.mm"
include "spcgv.mm"
include "mpd.mm"
include "mtod.mm"

theorem nnlim
  let cA: class A
  let vx: setvar x


  assert |- ( A e. _om -> -. Lim A )

  proof
    cA
    com
    wcel
    #
    cA
    wlim
    #
    cA
    cA
    wcel
    #
    @0
    cA
    word
    @2
    wn
    cA
    nnord
    cA
    ordirr
    syl
    @0
    vx
    cv
    #
    wlim
    #
    cA
    @3
    wcel
    #
    wi
    #
    vx
    wal
    #
    @1
    @2
    wi
    #
    @0
    cA
    con0
    wcel
    @7
    vx
    cA
    elom
    simprbi
    @6
    @8
    vx
    cA
    com
    @3
    cA
    wceq
    @4
    @1
    @5
    @2
    @3
    cA
    limeq
    @3
    cA
    cA
    eleq2
    imbi12d
    spcgv
    mpd
    mtod
end
