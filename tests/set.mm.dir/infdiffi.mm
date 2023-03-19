include "cfn.mm"
include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cdif.mm"
include "cen.mm"
include "cv.mm"
include "wi.mm"
include "csn.mm"
include "c0.mm"
include "wceq.mm"
include "difeq2.mm"
include "dif0.mm"
include "syl6eq.mm"
include "breq1d.mm"
include "imbi2d.mm"
include "cun.mm"
include "difun1.mm"
include "cvv.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "enrefg.mm"
include "syl.mm"
include "wa.mm"
include "domen2.mm"
include "biimparc.mm"
include "infdifsn.mm"
include "entr.mm"
include "sylancom.mm"
include "ex.mm"
include "a2i.mm"
include "a1i.mm"
include "findcard2.mm"
include "impcom.mm"

theorem infdiffi
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( _om ~<_ A /\ B e. Fin ) -> ( A \ B ) ~~ A )

  proof
    cB
    cfn
    wcel
    com
    cA
    cdom
    wbr
    #
    cA
    cB
    cdif
    #
    cA
    cen
    wbr
    #
    @0
    cA
    vx
    cv
    #
    cdif
    #
    cA
    cen
    wbr
    #
    wi
    @0
    cA
    cA
    cen
    wbr
    #
    wi
    @0
    cA
    vy
    cv
    #
    cdif
    #
    cA
    cen
    wbr
    #
    wi
    #
    @0
    @8
    vz
    cv
    #
    csn
    #
    cdif
    #
    cA
    cen
    wbr
    #
    wi
    #
    @0
    @2
    wi
    vx
    vy
    vz
    cB
    @3
    c0
    wceq
    #
    @5
    @6
    @0
    @16
    @4
    cA
    cA
    cen
    @16
    @4
    cA
    c0
    cdif
    cA
    @3
    c0
    cA
    difeq2
    cA
    dif0
    syl6eq
    breq1d
    imbi2d
    @3
    @7
    wceq
    #
    @5
    @9
    @0
    @17
    @4
    @8
    cA
    cen
    @3
    @7
    cA
    difeq2
    breq1d
    imbi2d
    @3
    @7
    @12
    cun
    #
    wceq
    #
    @5
    @14
    @0
    @19
    @4
    @13
    cA
    cen
    @19
    @4
    cA
    @18
    cdif
    @13
    @3
    @18
    cA
    difeq2
    cA
    @7
    @12
    difun1
    syl6eq
    breq1d
    imbi2d
    @3
    cB
    wceq
    #
    @5
    @2
    @0
    @20
    @4
    @1
    cA
    cen
    @3
    cB
    cA
    difeq2
    breq1d
    imbi2d
    @0
    cA
    cvv
    wcel
    @6
    com
    cA
    cdom
    reldom
    brrelex2i
    cA
    cvv
    enrefg
    syl
    @10
    @15
    wi
    @7
    cfn
    wcel
    @0
    @9
    @14
    @0
    @9
    @14
    @0
    @9
    @13
    @8
    cen
    wbr
    #
    @14
    @0
    @9
    wa
    com
    @8
    cdom
    wbr
    #
    @21
    @9
    @22
    @0
    @8
    cA
    com
    domen2
    biimparc
    @8
    @11
    infdifsn
    syl
    @13
    @8
    cA
    entr
    sylancom
    ex
    a2i
    a1i
    findcard2
    impcom
end
