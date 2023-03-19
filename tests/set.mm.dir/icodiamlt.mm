include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cico.mm"
include "co.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "w3a.mm"
include "cxr.mm"
include "wi.mm"
include "rexr.mm"
include "elico2.mm"
include "anbi12d.mm"
include "biimpd.mm"
include "sylan2.mm"
include "cneg.mm"
include "simplr.mm"
include "recnd.mm"
include "simpll.mm"
include "negsubdi2d.mm"
include "resubcld.mm"
include "simprl1.mm"
include "simprr1.mm"
include "simprl2.mm"
include "lesub1dd.mm"
include "simprr3.mm"
include "ltsub2dd.mm"
include "lelttrd.mm"
include "eqbrtrd.mm"
include "simprl3.mm"
include "ltsub1dd.mm"
include "simprr2.mm"
include "lesub2dd.mm"
include "ltletrd.mm"
include "absltd.mm"
include "mpbir2and.mm"
include "ex.mm"
include "syld.mm"
include "imp.mm"

theorem icodiamlt
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( C e. ( A [,) B ) /\ D e. ( A [,) B ) ) ) -> ( abs ` ( C - D ) ) < ( B - A ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cC
    cA
    cB
    cico
    co
    #
    wcel
    #
    cD
    @3
    wcel
    #
    wa
    #
    cC
    cD
    cmin
    co
    #
    cabs
    cfv
    cB
    cA
    cmin
    co
    #
    clt
    wbr
    #
    @2
    @6
    cC
    cr
    wcel
    #
    cA
    cC
    cle
    wbr
    #
    cC
    cB
    clt
    wbr
    #
    w3a
    #
    cD
    cr
    wcel
    #
    cA
    cD
    cle
    wbr
    #
    cD
    cB
    clt
    wbr
    #
    w3a
    #
    wa
    #
    @9
    @1
    @0
    cB
    cxr
    wcel
    #
    @6
    @18
    wi
    cB
    rexr
    @0
    @19
    wa
    #
    @6
    @18
    @20
    @4
    @13
    @5
    @17
    cA
    cB
    cC
    elico2
    cA
    cB
    cD
    elico2
    anbi12d
    biimpd
    sylan2
    @2
    @18
    @9
    @2
    @18
    wa
    #
    @9
    @8
    cneg
    #
    @7
    clt
    wbr
    @7
    @8
    clt
    wbr
    @21
    @22
    cA
    cB
    cmin
    co
    #
    @7
    clt
    @21
    cB
    cA
    @21
    cB
    @0
    @1
    @18
    simplr
    #
    recnd
    @21
    cA
    @0
    @1
    @18
    simpll
    #
    recnd
    negsubdi2d
    @21
    @23
    cC
    cB
    cmin
    co
    @7
    @21
    cA
    cB
    @25
    @24
    resubcld
    @21
    cC
    cB
    @10
    @11
    @12
    @17
    @2
    simprl1
    #
    @24
    resubcld
    @21
    cC
    cD
    @26
    @14
    @15
    @16
    @13
    @2
    simprr1
    #
    resubcld
    #
    @21
    cA
    cC
    cB
    @25
    @26
    @24
    @10
    @11
    @12
    @17
    @2
    simprl2
    lesub1dd
    @21
    cD
    cB
    cC
    @27
    @24
    @26
    @14
    @15
    @16
    @13
    @2
    simprr3
    ltsub2dd
    lelttrd
    eqbrtrd
    @21
    @7
    cB
    cD
    cmin
    co
    @8
    @28
    @21
    cB
    cD
    @24
    @27
    resubcld
    @21
    cB
    cA
    @24
    @25
    resubcld
    #
    @21
    cC
    cB
    cD
    @26
    @24
    @27
    @10
    @11
    @12
    @17
    @2
    simprl3
    ltsub1dd
    @21
    cA
    cD
    cB
    @25
    @27
    @24
    @14
    @15
    @16
    @13
    @2
    simprr2
    lesub2dd
    ltletrd
    @21
    @7
    @8
    @28
    @29
    absltd
    mpbir2and
    ex
    syld
    imp
end
