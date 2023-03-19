include "wdisj.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "wal.mm"
include "dfdisj2.mm"
include "wnf.mm"
include "wtru.mm"
include "nftru.mm"
include "weq.mm"
include "wn.mm"
include "nfcvf.mm"
include "wnfc.mm"
include "a1i.mm"
include "nfeld.mm"
include "nfcri.mm"
include "nfand.mm"
include "adantl.mm"
include "nfmod2.mm"
include "trud.mm"
include "nfal.mm"
include "nfxfr.mm"

theorem nfdisj
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  assume nfdisj.1: |- F/_ y A
  assume nfdisj.2: |- F/_ y B


  assert |- F/ y Disj_ x e. A B

  proof
    vx
    cA
    cB
    wdisj
    vx
    cv
    #
    cA
    wcel
    #
    vz
    cv
    cB
    wcel
    #
    wa
    #
    vx
    wmo
    #
    vz
    wal
    vy
    vx
    vz
    cA
    cB
    dfdisj2
    @4
    vy
    vz
    @4
    vy
    wnf
    wtru
    @3
    vy
    vx
    vx
    nftru
    vy
    vx
    weq
    vy
    wal
    wn
    #
    @3
    vy
    wnf
    wtru
    @5
    @1
    @2
    vy
    @5
    vy
    @0
    cA
    vy
    vx
    nfcvf
    vy
    cA
    wnfc
    @5
    nfdisj.1
    a1i
    nfeld
    @2
    vy
    wnf
    @5
    vy
    vz
    cB
    nfdisj.2
    nfcri
    a1i
    nfand
    adantl
    nfmod2
    trud
    nfal
    nfxfr
end
