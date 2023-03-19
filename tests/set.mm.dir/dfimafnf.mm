include "wfun.mm"
include "cdm.mm"
include "wss.mm"
include "wa.mm"
include "cima.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "wbr.mm"
include "wcel.mm"
include "wb.mm"
include "ssel.mm"
include "eqcom.mm"
include "funbrfvb.mm"
include "syl5bbr.mm"
include "ex.mm"
include "syl9r.mm"
include "imp31.mm"
include "rexbidva.mm"
include "abbidv.mm"
include "dfima2.mm"
include "syl6reqr.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfeq2.mm"
include "nfv.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "cbvrexf.mm"
include "abbii.mm"
include "syl6eq.mm"

theorem dfimafnf
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let vz: setvar z
  assume dfimafnf.1: |- F/_ x A
  assume dfimafnf.2: |- F/_ x F

  disjoint x y
  disjoint A y
  disjoint F y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint F z
  assert |- ( ( Fun F /\ A C_ dom F ) -> ( F " A ) = { y | E. x e. A y = ( F ` x ) } )

  proof
    cF
    wfun
    #
    cA
    cF
    cdm
    #
    wss
    #
    wa
    #
    cF
    cA
    cima
    #
    vy
    cv
    #
    vz
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vz
    cA
    wrex
    #
    vy
    cab
    #
    @5
    vx
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cab
    @3
    @10
    @6
    @5
    cF
    wbr
    #
    vz
    cA
    wrex
    #
    vy
    cab
    @4
    @3
    @9
    @16
    vy
    @3
    @8
    @15
    vz
    cA
    @0
    @2
    @6
    cA
    wcel
    #
    @8
    @15
    wb
    #
    @2
    @17
    @6
    @1
    wcel
    #
    @0
    @18
    cA
    @1
    @6
    ssel
    @0
    @19
    @18
    @8
    @7
    @5
    wceq
    @0
    @19
    wa
    @15
    @7
    @5
    eqcom
    @6
    @5
    cF
    funbrfvb
    syl5bbr
    ex
    syl9r
    imp31
    rexbidva
    abbidv
    vz
    vy
    cF
    cA
    dfima2
    syl6reqr
    @9
    @14
    vy
    @8
    @13
    vz
    vx
    cA
    vz
    cA
    nfcv
    dfimafnf.1
    vx
    @5
    @7
    vx
    @6
    cF
    dfimafnf.2
    vx
    @6
    nfcv
    nffv
    nfeq2
    @13
    vz
    nfv
    @6
    @11
    wceq
    @7
    @12
    @5
    @6
    @11
    cF
    fveq2
    eqeq2d
    cbvrexf
    abbii
    syl6eq
end
