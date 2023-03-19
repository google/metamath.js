include "ccmp.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "cuni.mm"
include "wceq.mm"
include "crab.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wss.mm"
include "dfss3.mm"
include "elunirab.mm"
include "ralbii.mm"
include "sylbbr.mm"
include "ssrab2.mm"
include "unissi.mm"
include "sseqtr4i.mm"
include "a1i.mm"
include "eqssd.mm"
include "cmpcov.mm"
include "mp3an2.mm"
include "sylan2.mm"
include "ssrab.mm"
include "anbi1i.mm"
include "an32.mm"
include "anass.mm"
include "3bitri.mm"
include "3bitr4i.mm"
include "elfpw.mm"
include "rexbii2.mm"
include "sylib.mm"

theorem cmpcov2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cJ: class J
  let cX: class X
  let vs: setvar s
  let vf: setvar f
  let vu: setvar u
  let vz: setvar z
  let cA: class A
  let vr: setvar r
  let wps: wff ps
  let cS: class S
  assume iscmp.1: |- X = U. J

  disjoint s x
  disjoint s y
  disjoint x y
  disjoint J s
  disjoint J x
  disjoint J y
  disjoint ph s
  disjoint ph x
  disjoint X x
  disjoint f s
  disjoint f u
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint s u
  disjoint s z
  disjoint A s
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint r s
  disjoint r u
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint J r
  disjoint J u
  disjoint J z
  disjoint f ph
  disjoint ph u
  disjoint ps s
  disjoint ps u
  disjoint ps z
  disjoint S r
  disjoint S s
  disjoint X r
  disjoint X u
  assert |- ( ( J e. Comp /\ A. x e. X E. y e. J ( x e. y /\ ph ) ) -> E. s e. ( ~P J i^i Fin ) ( X = U. s /\ A. y e. s ph ) )

  proof
    cJ
    ccmp
    wcel
    #
    vx
    cv
    #
    vy
    cv
    wcel
    wph
    wa
    vy
    cJ
    wrex
    #
    vx
    cX
    wral
    #
    wa
    cX
    vs
    cv
    #
    cuni
    wceq
    #
    vs
    wph
    vy
    cJ
    crab
    #
    cpw
    cfn
    cin
    #
    wrex
    #
    @5
    wph
    vy
    @4
    wral
    #
    wa
    #
    vs
    cJ
    cpw
    cfn
    cin
    #
    wrex
    @3
    @0
    cX
    @6
    cuni
    #
    wceq
    #
    @8
    @3
    cX
    @12
    cX
    @12
    wss
    @1
    @12
    wcel
    #
    vx
    cX
    wral
    @3
    vx
    cX
    @12
    dfss3
    @14
    @2
    vx
    cX
    wph
    vy
    @1
    cJ
    elunirab
    ralbii
    sylbbr
    @12
    cX
    wss
    @3
    @12
    cJ
    cuni
    cX
    @6
    cJ
    wph
    vy
    cJ
    ssrab2
    #
    unissi
    iscmp.1
    sseqtr4i
    a1i
    eqssd
    @0
    @6
    cJ
    wss
    @13
    @8
    @15
    @6
    cJ
    cX
    vs
    iscmp.1
    cmpcov
    mp3an2
    sylan2
    @5
    @10
    vs
    @7
    @11
    @4
    @6
    wss
    #
    @4
    cfn
    wcel
    #
    wa
    #
    @5
    wa
    #
    @4
    cJ
    wss
    #
    @17
    wa
    #
    @10
    wa
    #
    @4
    @7
    wcel
    #
    @5
    wa
    @4
    @11
    wcel
    #
    @10
    wa
    @16
    @5
    wa
    #
    @17
    wa
    @20
    @10
    wa
    #
    @17
    wa
    @19
    @22
    @25
    @26
    @17
    @25
    @20
    @9
    wa
    #
    @5
    wa
    @20
    @5
    wa
    @9
    wa
    @26
    @16
    @27
    @5
    wph
    vy
    cJ
    @4
    ssrab
    anbi1i
    @20
    @9
    @5
    an32
    @20
    @5
    @9
    anass
    3bitri
    anbi1i
    @16
    @17
    @5
    an32
    @20
    @17
    @10
    an32
    3bitr4i
    @23
    @18
    @5
    @4
    @6
    elfpw
    anbi1i
    @24
    @21
    @10
    @4
    cJ
    elfpw
    anbi1i
    3bitr4i
    rexbii2
    sylib
end
