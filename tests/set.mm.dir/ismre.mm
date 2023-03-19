include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "cvv.mm"
include "cpw.mm"
include "wss.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cint.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "elfvex.mm"
include "elex.mm"
include "3ad2ant2.mm"
include "wa.mm"
include "crab.mm"
include "wel.mm"
include "wceq.mm"
include "pweq.mm"
include "pweqd.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "rabeqbidv.mm"
include "df-mre.mm"
include "vpwex.mm"
include "pwex.mm"
include "rabex.mm"
include "fvmpt3i.mm"
include "eleq2d.mm"
include "wb.mm"
include "eleq2.mm"
include "imbi2d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "elrab.mm"
include "a1i.mm"
include "pwexg.mm"
include "elpw2g.mm"
include "syl.mm"
include "3anass.mm"
include "syl6bbr.mm"
include "3bitrd.mm"
include "pm5.21nii.mm"

theorem ismre
  let cC: class C
  let cX: class X
  let vs: setvar s
  let vc: setvar c
  let vx: setvar x
  let cS: class S

  disjoint C s
  disjoint X s
  disjoint C c
  disjoint C x
  disjoint c s
  disjoint c x
  disjoint s x
  disjoint X c
  disjoint X x
  disjoint S c
  disjoint S s
  disjoint S x
  assert |- ( C e. ( Moore ` X ) <-> ( C C_ ~P X /\ X e. C /\ A. s e. ~P C ( s =/= (/) -> |^| s e. C ) ) )

  proof
    cC
    cX
    cmre
    cfv
    #
    wcel
    #
    cX
    cvv
    wcel
    #
    cC
    cX
    cpw
    #
    wss
    #
    cX
    cC
    wcel
    #
    vs
    cv
    #
    c0
    wne
    #
    @6
    cint
    #
    cC
    wcel
    #
    wi
    #
    vs
    cC
    cpw
    #
    wral
    #
    w3a
    #
    cC
    cX
    cmre
    elfvex
    @5
    @4
    @2
    @12
    cX
    cC
    elex
    3ad2ant2
    @2
    @1
    cC
    cX
    vc
    cv
    #
    wcel
    #
    @7
    @8
    @14
    wcel
    #
    wi
    #
    vs
    @14
    cpw
    #
    wral
    #
    wa
    #
    vc
    @3
    cpw
    #
    crab
    #
    wcel
    #
    cC
    @21
    wcel
    #
    @5
    @12
    wa
    #
    wa
    #
    @13
    @2
    @0
    @22
    cC
    vx
    cX
    vx
    vc
    wel
    #
    @19
    wa
    #
    vc
    vx
    cv
    #
    cpw
    #
    cpw
    #
    crab
    @22
    cvv
    cmre
    @29
    cX
    wceq
    #
    @28
    @20
    vc
    @31
    @21
    @32
    @30
    @3
    @29
    cX
    pweq
    pweqd
    @32
    @27
    @15
    @19
    @29
    cX
    @14
    eleq1
    anbi1d
    rabeqbidv
    vx
    vs
    vc
    df-mre
    @28
    vc
    @31
    @30
    vx
    vpwex
    pwex
    rabex
    fvmpt3i
    eleq2d
    @23
    @26
    wb
    @2
    @20
    @25
    vc
    cC
    @21
    @14
    cC
    wceq
    #
    @15
    @5
    @19
    @12
    @14
    cC
    cX
    eleq2
    @33
    @17
    @10
    vs
    @18
    @11
    @14
    cC
    pweq
    @33
    @16
    @9
    @7
    @14
    cC
    @8
    eleq2
    imbi2d
    raleqbidv
    anbi12d
    elrab
    a1i
    @2
    @26
    @4
    @25
    wa
    @13
    @2
    @24
    @4
    @25
    @2
    @3
    cvv
    wcel
    @24
    @4
    wb
    cX
    cvv
    pwexg
    cC
    @3
    cvv
    elpw2g
    syl
    anbi1d
    @4
    @5
    @12
    3anass
    syl6bbr
    3bitrd
    pm5.21nii
end
