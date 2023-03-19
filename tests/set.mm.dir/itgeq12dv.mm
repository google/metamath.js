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
include "oveq1d.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "pm5.32da.mm"
include "eleq2d.mm"
include "anbi1d.mm"
include "bitrd.mm"
include "wceq.mm"
include "adantrr.mm"
include "wn.mm"
include "eqidd.mm"
include "ifbieq12d2.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "sumeq2sdv.mm"
include "eqid.mm"
include "dfitg.mm"
include "3eqtr4g.mm"

theorem itgeq12dv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  assume itgeq12dv.2: |- ( ph -> A = B )
  assume itgeq12dv.1: |- ( ( ph /\ x e. A ) -> C = D )

  disjoint ph x
  disjoint k x
  disjoint k ph
  disjoint A k
  disjoint B k
  disjoint C k
  disjoint D k
  assert |- ( ph -> S. A C _d x = S. B D _d x )

  proof
    wph
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
    @1
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
    @1
    vx
    cr
    @2
    cB
    wcel
    #
    cc0
    cD
    @1
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
    @14
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
    cD
    citg
    wph
    @0
    @11
    @20
    vk
    wph
    @10
    @19
    @1
    cmul
    wph
    @9
    @18
    citg2
    wph
    vx
    cr
    @8
    @17
    wph
    @7
    @16
    @5
    cc0
    @14
    cc0
    wph
    @7
    @3
    @15
    wa
    @16
    wph
    @3
    @6
    @15
    wph
    @3
    wa
    #
    @5
    @14
    cc0
    cle
    @21
    @4
    @13
    cre
    @21
    cC
    cD
    @1
    cdiv
    itgeq12dv.1
    oveq1d
    fveq2d
    #
    breq2d
    pm5.32da
    wph
    @3
    @12
    @15
    wph
    cA
    cB
    @2
    itgeq12dv.2
    eleq2d
    anbi1d
    bitrd
    wph
    @3
    @5
    @14
    wceq
    @6
    @22
    adantrr
    wph
    @7
    wn
    wa
    cc0
    eqidd
    ifbieq12d2
    mpteq2dv
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
    dfitg
    vx
    cB
    cD
    @14
    vk
    @14
    eqid
    dfitg
    3eqtr4g
end
