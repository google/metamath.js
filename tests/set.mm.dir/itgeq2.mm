include "wceq.mm"
include "wral.mm"
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
include "eqid.mm"
include "wi.mm"
include "wn.mm"
include "simpl.mm"
include "con3i.mm"
include "iffalsed.mm"
include "eqtr4d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "anbi2d.mm"
include "ifbieq1d.mm"
include "ja.mm"
include "a1d.mm"
include "ralimi2.mm"
include "mpteq12.mm"
include "sylancr.mm"
include "oveq2d.mm"
include "sumeq2sdv.mm"
include "dfitg.mm"
include "3eqtr4g.mm"

theorem itgeq2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k


  assert |- ( A. x e. A B = C -> S. A B _d x = S. A C _d x )

  proof
    cB
    cC
    wceq
    #
    vx
    cA
    wral
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
    cB
    @3
    cdiv
    co
    #
    cre
    cfv
    #
    cle
    wbr
    #
    wa
    #
    @7
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
    @2
    @3
    vx
    cr
    @5
    cc0
    cC
    @3
    cdiv
    co
    #
    cre
    cfv
    #
    cle
    wbr
    #
    wa
    #
    @15
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
    cA
    cC
    citg
    @1
    @2
    @13
    @21
    vk
    @1
    @12
    @20
    @3
    cmul
    @1
    @11
    @19
    citg2
    @1
    cr
    cr
    wceq
    @10
    @18
    wceq
    #
    vx
    cr
    wral
    @11
    @19
    wceq
    cr
    eqid
    @0
    @22
    vx
    cA
    cr
    @5
    @0
    wi
    @22
    @4
    cr
    wcel
    @5
    @0
    @22
    @5
    wn
    #
    @10
    cc0
    @18
    @23
    @9
    @7
    cc0
    @9
    @5
    @5
    @8
    simpl
    con3i
    iffalsed
    @23
    @17
    @15
    cc0
    @17
    @5
    @5
    @16
    simpl
    con3i
    iffalsed
    eqtr4d
    @0
    @9
    @17
    @7
    @15
    cc0
    @0
    @8
    @16
    @5
    @0
    @7
    @15
    cc0
    cle
    @0
    @6
    @14
    cre
    cB
    cC
    @3
    cdiv
    oveq1
    fveq2d
    #
    breq2d
    anbi2d
    @24
    ifbieq1d
    ja
    a1d
    ralimi2
    vx
    cr
    @10
    cr
    @18
    mpteq12
    sylancr
    fveq2d
    oveq2d
    sumeq2sdv
    vx
    cA
    cB
    @7
    vk
    @7
    eqid
    dfitg
    vx
    cA
    cC
    @15
    vk
    @15
    eqid
    dfitg
    3eqtr4g
end
