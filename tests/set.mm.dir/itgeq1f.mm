include "wceq.mm"
include "cc0.mm"
include "c3.mm"
include "cfz.mm"
include "co.mm"
include "ci.mm"
include "cv.mm"
include "cexp.mm"
include "cr.mm"
include "wcel.mm"
include "cdiv.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "cmul.mm"
include "csu.mm"
include "citg.mm"
include "wral.mm"
include "eqid.mm"
include "nfeq.mm"
include "eleq2.mm"
include "anbi1d.mm"
include "ifbid.mm"
include "a1d.mm"
include "ralrimi.mm"
include "mpteq12.mm"
include "sylancr.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "sumeq2sdv.mm"
include "dfitg.mm"
include "3eqtr4g.mm"

theorem itgeq1f
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vy: setvar y
  assume itgeq1f.1: |- F/_ x A
  assume itgeq1f.2: |- F/_ x B


  assert |- ( A = B -> S. A C _d x = S. B C _d x )

  proof
    cA
    cB
    wceq
    #
    cc0
    c3
    cfz
    co
    #
    ci
    vk
    cv
    cexp
    co
    #
    vx
    cr
    vx
    cv
    #
    cA
    wcel
    #
    cc0
    cC
    @2
    cdiv
    co
    cre
    cfv
    #
    cle
    wbr
    #
    wa
    #
    @5
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cmul
    co
    #
    vk
    csu
    @1
    @2
    vx
    cr
    @3
    cB
    wcel
    #
    @6
    wa
    #
    @5
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cmul
    co
    #
    vk
    csu
    vx
    cA
    cC
    citg
    vx
    cB
    cC
    citg
    @0
    @1
    @11
    @17
    vk
    @0
    @10
    @16
    @2
    cmul
    @0
    @9
    @15
    citg2
    @0
    cr
    cr
    wceq
    @8
    @14
    wceq
    #
    vx
    cr
    wral
    @9
    @15
    wceq
    cr
    eqid
    @0
    @18
    vx
    cr
    vx
    cA
    cB
    itgeq1f.1
    itgeq1f.2
    nfeq
    @0
    @18
    @3
    cr
    wcel
    @0
    @7
    @13
    @5
    cc0
    @0
    @4
    @12
    @6
    cA
    cB
    @3
    eleq2
    anbi1d
    ifbid
    a1d
    ralrimi
    vx
    cr
    @8
    cr
    @14
    mpteq12
    sylancr
    fveq2d
    oveq2d
    sumeq2sdv
    vx
    cA
    cC
    @5
    vk
    @5
    eqid
    #
    dfitg
    vx
    cB
    cC
    @5
    vk
    @19
    dfitg
    3eqtr4g
end
