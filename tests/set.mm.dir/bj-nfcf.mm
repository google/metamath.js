include "wnfc.mm"
include "cv.mm"
include "wcel.mm"
include "wnf.mm"
include "wal.mm"
include "df-nfc.mm"
include "wsb.mm"
include "nfcri.mm"
include "nfnf.mm"
include "sb8.mm"
include "bj-sbnf.mm"
include "clelsb3.mm"
include "nfbii.mm"
include "bitri.mm"
include "albii.mm"

theorem bj-nfcf
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume bj-nfcf.nf: |- F/_ y A

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- ( F/_ x A <-> A. y F/ x y e. A )

  proof
    vx
    cA
    wnfc
    vz
    cv
    cA
    wcel
    #
    vx
    wnf
    #
    vz
    wal
    #
    vy
    cv
    cA
    wcel
    #
    vx
    wnf
    #
    vy
    wal
    #
    vx
    vz
    cA
    df-nfc
    @2
    @1
    vz
    vy
    wsb
    #
    vy
    wal
    @5
    @1
    vz
    vy
    @0
    vy
    vx
    vy
    vz
    cA
    bj-nfcf.nf
    nfcri
    nfnf
    sb8
    @6
    @4
    vy
    @6
    @0
    vz
    vy
    wsb
    #
    vx
    wnf
    @4
    @0
    vx
    vz
    vy
    bj-sbnf
    @7
    @3
    vx
    vy
    vz
    cA
    clelsb3
    nfbii
    bitri
    albii
    bitri
    bitri
end
