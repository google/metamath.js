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
include "cin.mm"
include "citg.mm"
include "simpr.mm"
include "biantrud.mm"
include "elin.mm"
include "syl6bbr.mm"
include "anbi1d.mm"
include "ifbid.mm"
include "mpteq2dva.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "sumeq2i.mm"
include "eqid.mm"
include "dfitg.mm"
include "3eqtr4i.mm"

theorem itgresr
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cC: class C


  assert |- S. A B _d x = S. ( A i^i RR ) B _d x

  proof
    cc0
    c3
    cfz
    co
    #
    ci
    vk
    cv
    #
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
    cB
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
    @0
    @2
    vx
    cr
    @3
    cA
    cr
    cin
    #
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
    cB
    citg
    vx
    @12
    cB
    citg
    @0
    @11
    @18
    vk
    @1
    @0
    wcel
    #
    @10
    @17
    @2
    cmul
    @19
    @9
    @16
    citg2
    @19
    vx
    cr
    @8
    @15
    @19
    @3
    cr
    wcel
    #
    wa
    #
    @7
    @14
    @5
    cc0
    @21
    @4
    @13
    @6
    @21
    @4
    @4
    @20
    wa
    @13
    @21
    @20
    @4
    @19
    @20
    simpr
    biantrud
    @3
    cA
    cr
    elin
    syl6bbr
    anbi1d
    ifbid
    mpteq2dva
    fveq2d
    oveq2d
    sumeq2i
    vx
    cA
    cB
    @5
    vk
    @5
    eqid
    #
    dfitg
    vx
    @12
    cB
    @5
    vk
    @22
    dfitg
    3eqtr4i
end
