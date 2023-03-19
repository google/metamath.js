include "cdm.mm"
include "wss.mm"
include "wfun.mm"
include "cima.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "dfss2.mm"
include "wceq.mm"
include "wrex.mm"
include "wbr.mm"
include "eqcom.mm"
include "ssel.mm"
include "funbrfvb.mm"
include "ex.mm"
include "syl9.mm"
include "imp31.mm"
include "syl5bb.mm"
include "rexbidva.mm"
include "vex.mm"
include "elima.mm"
include "syl6rbbr.mm"
include "imbi1d.mm"
include "r19.23v.mm"
include "syl6bbr.mm"
include "albidv.mm"
include "ralcom4.mm"
include "fvex.mm"
include "eleq1.mm"
include "ceqsalv.mm"
include "ralbii.mm"
include "bitr3i.mm"
include "syl6bb.mm"
include "ancoms.mm"

theorem funimass4
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y
  let cY: class Y

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint F y
  disjoint Y x
  assert |- ( ( Fun F /\ A C_ dom F ) -> ( ( F " A ) C_ B <-> A. x e. A ( F ` x ) e. B ) )

  proof
    cA
    cF
    cdm
    #
    wss
    #
    cF
    wfun
    #
    cF
    cA
    cima
    #
    cB
    wss
    #
    vx
    cv
    #
    cF
    cfv
    #
    cB
    wcel
    #
    vx
    cA
    wral
    #
    wb
    @4
    vy
    cv
    #
    @3
    wcel
    #
    @9
    cB
    wcel
    #
    wi
    #
    vy
    wal
    #
    @1
    @2
    wa
    #
    @8
    vy
    @3
    cB
    dfss2
    @14
    @13
    @9
    @6
    wceq
    #
    @11
    wi
    #
    vx
    cA
    wral
    #
    vy
    wal
    #
    @8
    @14
    @12
    @17
    vy
    @14
    @12
    @15
    vx
    cA
    wrex
    #
    @11
    wi
    @17
    @14
    @10
    @19
    @11
    @14
    @19
    @5
    @9
    cF
    wbr
    #
    vx
    cA
    wrex
    @10
    @14
    @15
    @20
    vx
    cA
    @15
    @6
    @9
    wceq
    #
    @14
    @5
    cA
    wcel
    #
    wa
    @20
    @9
    @6
    eqcom
    @1
    @2
    @22
    @21
    @20
    wb
    #
    @1
    @22
    @5
    @0
    wcel
    #
    @2
    @23
    cA
    @0
    @5
    ssel
    @2
    @24
    @23
    @5
    @9
    cF
    funbrfvb
    ex
    syl9
    imp31
    syl5bb
    rexbidva
    vx
    @9
    cF
    cA
    vy
    vex
    elima
    syl6rbbr
    imbi1d
    @15
    @11
    vx
    cA
    r19.23v
    syl6bbr
    albidv
    @18
    @16
    vy
    wal
    #
    vx
    cA
    wral
    @8
    @16
    vx
    vy
    cA
    ralcom4
    @25
    @7
    vx
    cA
    @11
    @7
    vy
    @6
    @5
    cF
    fvex
    @9
    @6
    cB
    eleq1
    ceqsalv
    ralbii
    bitr3i
    syl6bb
    syl5bb
    ancoms
end
