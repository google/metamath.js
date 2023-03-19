include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ckq.mm"
include "ct1.mm"
include "wa.mm"
include "wel.mm"
include "wi.mm"
include "wral.mm"
include "wb.mm"
include "cv.mm"
include "crab.mm"
include "cmpt.mm"
include "eqid.mm"
include "isr0.mm"
include "biimpa.mm"
include "wceq.mm"
include "eleq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "bibi1d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "bibi2d.mm"
include "rspc2v.mm"
include "mpan9.mm"

theorem r0sep
  let cA: class A
  let cB: class B
  let vo: setvar o
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vb: setvar b
  let vj: setvar j
  let vw: setvar w
  let vz: setvar z

  disjoint A o
  disjoint B o
  disjoint J o
  disjoint X o
  disjoint o x
  disjoint o y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint a b
  disjoint a j
  disjoint a o
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint J a
  disjoint b j
  disjoint b o
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint J b
  disjoint j o
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint J j
  disjoint o w
  disjoint o z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint J w
  disjoint x z
  disjoint J x
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ( ( J e. ( TopOn ` X ) /\ ( KQ ` J ) e. Fre ) /\ ( A e. X /\ B e. X ) ) -> ( A. o e. J ( A e. o -> B e. o ) -> A. o e. J ( A e. o <-> B e. o ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cJ
    ckq
    cfv
    ct1
    wcel
    #
    wa
    vx
    vo
    wel
    #
    vy
    vo
    wel
    #
    wi
    #
    vo
    cJ
    wral
    #
    @2
    @3
    wb
    #
    vo
    cJ
    wral
    #
    wi
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    cA
    cX
    wcel
    cB
    cX
    wcel
    wa
    cA
    vo
    cv
    #
    wcel
    #
    cB
    @10
    wcel
    #
    wi
    #
    vo
    cJ
    wral
    #
    @11
    @12
    wb
    #
    vo
    cJ
    wral
    #
    wi
    #
    @0
    @1
    @9
    vz
    vw
    vx
    vy
    vo
    vz
    cX
    vz
    vw
    wel
    vw
    cJ
    crab
    cmpt
    #
    cJ
    cX
    @18
    eqid
    isr0
    biimpa
    @8
    @17
    @11
    @3
    wi
    #
    vo
    cJ
    wral
    #
    @11
    @3
    wb
    #
    vo
    cJ
    wral
    #
    wi
    vx
    vy
    cA
    cB
    cX
    cX
    vx
    cv
    #
    cA
    wceq
    #
    @5
    @20
    @7
    @22
    @24
    @4
    @19
    vo
    cJ
    @24
    @2
    @11
    @3
    @23
    cA
    @10
    eleq1
    #
    imbi1d
    ralbidv
    @24
    @6
    @21
    vo
    cJ
    @24
    @2
    @11
    @3
    @25
    bibi1d
    ralbidv
    imbi12d
    vy
    cv
    #
    cB
    wceq
    #
    @20
    @14
    @22
    @16
    @27
    @19
    @13
    vo
    cJ
    @27
    @3
    @12
    @11
    @26
    cB
    @10
    eleq1
    #
    imbi2d
    ralbidv
    @27
    @21
    @15
    vo
    cJ
    @27
    @3
    @12
    @11
    @28
    bibi2d
    ralbidv
    imbi12d
    rspc2v
    mpan9
end
