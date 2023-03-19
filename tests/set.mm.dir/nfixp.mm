include "cixp.mm"
include "cv.mm"
include "wcel.mm"
include "cab.mm"
include "wfn.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "df-ixp.mm"
include "nfcv.mm"
include "wnfc.mm"
include "wtru.mm"
include "nftru.mm"
include "weq.mm"
include "wal.mm"
include "wn.mm"
include "nfcvf.mm"
include "adantl.mm"
include "a1i.mm"
include "nfeld.mm"
include "nfabd2.mm"
include "trud.mm"
include "nffn.mm"
include "wi.mm"
include "df-ral.mm"
include "wnf.mm"
include "nffvd.mm"
include "nfimd.mm"
include "nfald2.mm"
include "nfxfr.mm"
include "nfan.mm"
include "nfab.mm"
include "nfcxfr.mm"

theorem nfixp
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  assume nfixp.1: |- F/_ y A
  assume nfixp.2: |- F/_ y B


  assert |- F/_ y X_ x e. A B

  proof
    vy
    vx
    cA
    cB
    cixp
    vz
    cv
    #
    vx
    cv
    #
    cA
    wcel
    #
    vx
    cab
    #
    wfn
    #
    @1
    @0
    cfv
    #
    cB
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    vz
    cab
    vx
    cA
    cB
    vz
    df-ixp
    @8
    vy
    vz
    @4
    @7
    vy
    vy
    @3
    @0
    vy
    @0
    nfcv
    #
    vy
    @3
    wnfc
    wtru
    @2
    vy
    vx
    vx
    nftru
    #
    wtru
    vy
    vx
    weq
    vy
    wal
    wn
    #
    wa
    #
    vy
    @1
    cA
    @11
    vy
    @1
    wnfc
    wtru
    vy
    vx
    nfcvf
    adantl
    #
    vy
    cA
    wnfc
    @12
    nfixp.1
    a1i
    nfeld
    #
    nfabd2
    trud
    nffn
    @7
    @2
    @6
    wi
    #
    vx
    wal
    #
    vy
    @6
    vx
    cA
    df-ral
    @16
    vy
    wnf
    wtru
    @15
    vy
    vx
    @10
    @12
    @2
    @6
    vy
    @14
    @12
    vy
    @5
    cB
    @12
    vy
    @1
    @0
    vy
    @0
    wnfc
    @12
    @9
    a1i
    @13
    nffvd
    vy
    cB
    wnfc
    @12
    nfixp.2
    a1i
    nfeld
    nfimd
    nfald2
    trud
    nfxfr
    nfan
    nfab
    nfcxfr
end
