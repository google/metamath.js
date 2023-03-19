include "wcel.mm"
include "w3a.mm"
include "wn.mm"
include "caov.mm"
include "cvv.mm"
include "cop.mm"
include "cdm.mm"
include "wceq.mm"
include "wa.mm"
include "cxp.mm"
include "eleq2i.mm"
include "opelxp.mm"
include "bitri.mm"
include "wi.mm"
include "aovvdm.mm"
include "3anass.mm"
include "simplbi2com.mm"
include "sylbi.mm"
include "syl.mm"
include "impcom.mm"
include "con3i.mm"
include "ndmaov.mm"
include "simpll.mm"
include "simprr.mm"
include "simplr.mm"
include "3jca.mm"
include "ex.mm"
include "syl11.mm"
include "imp.mm"
include "eqtr4d.mm"

theorem ndmaovdistr
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cF: class F
  let cG: class G
  let vk: setvar k
  let vx: setvar x
  assume ndmaov.1: |- dom F = ( S X. S )
  assume ndmaov.6: |- dom G = ( S X. S )


  assert |- ( -. ( A e. S /\ B e. S /\ C e. S ) -> (( A G (( B F C )) )) = (( (( A G B )) F (( A G C )) )) )

  proof
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    cC
    cS
    wcel
    #
    w3a
    #
    wn
    #
    cA
    cB
    cC
    cF
    caov
    #
    cG
    caov
    #
    cvv
    cA
    cB
    cG
    caov
    #
    cA
    cC
    cG
    caov
    #
    cF
    caov
    #
    @4
    cA
    @5
    cop
    #
    cG
    cdm
    #
    wcel
    #
    wn
    @6
    cvv
    wceq
    @12
    @3
    @12
    @0
    @5
    cS
    wcel
    #
    wa
    #
    @3
    @12
    @10
    cS
    cS
    cxp
    #
    wcel
    @14
    @11
    @15
    @10
    ndmaov.6
    eleq2i
    cA
    @5
    cS
    cS
    opelxp
    bitri
    @13
    @0
    @3
    @13
    cB
    cC
    cop
    #
    cF
    cdm
    #
    wcel
    #
    @0
    @3
    wi
    #
    cB
    cC
    cS
    cF
    aovvdm
    @18
    @1
    @2
    wa
    #
    @19
    @18
    @16
    @15
    wcel
    @20
    @17
    @15
    @16
    ndmaov.1
    eleq2i
    cB
    cC
    cS
    cS
    opelxp
    bitri
    @3
    @0
    @20
    @0
    @1
    @2
    3anass
    simplbi2com
    sylbi
    syl
    impcom
    sylbi
    con3i
    cA
    @5
    cG
    ndmaov
    syl
    @4
    @7
    @8
    cop
    #
    @17
    wcel
    #
    wn
    @9
    cvv
    wceq
    @22
    @3
    @22
    @7
    cS
    wcel
    #
    @8
    cS
    wcel
    #
    wa
    #
    @3
    @22
    @21
    @15
    wcel
    @25
    @17
    @15
    @21
    ndmaov.1
    eleq2i
    @7
    @8
    cS
    cS
    opelxp
    bitri
    @23
    @24
    @3
    @23
    cA
    cB
    cop
    #
    @11
    wcel
    #
    @24
    @3
    wi
    #
    cA
    cB
    cS
    cG
    aovvdm
    @27
    @0
    @1
    wa
    #
    @28
    @27
    @26
    @15
    wcel
    @29
    @11
    @15
    @26
    ndmaov.6
    eleq2i
    cA
    cB
    cS
    cS
    opelxp
    bitri
    cA
    cC
    cop
    #
    @11
    wcel
    #
    @29
    @3
    @24
    @31
    @0
    @2
    wa
    #
    @29
    @3
    wi
    @31
    @30
    @15
    wcel
    @32
    @11
    @15
    @30
    ndmaov.6
    eleq2i
    cA
    cC
    cS
    cS
    opelxp
    bitri
    @32
    @29
    @3
    @32
    @29
    wa
    @0
    @1
    @2
    @0
    @2
    @29
    simpll
    @32
    @0
    @1
    simprr
    @0
    @2
    @29
    simplr
    3jca
    ex
    sylbi
    cA
    cC
    cS
    cG
    aovvdm
    syl11
    sylbi
    syl
    imp
    sylbi
    con3i
    @7
    @8
    cF
    ndmaov
    syl
    eqtr4d
end
