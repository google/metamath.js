include "ccmp.mm"
include "wcel.mm"
include "cv.mm"
include "wrex.mm"
include "wa.mm"
include "wral.mm"
include "cuni.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wf.mm"
include "wex.mm"
include "simpl.mm"
include "cmpcov2.mm"
include "wss.mm"
include "wi.mm"
include "elfpw.mm"
include "simplrl.mm"
include "selpw.mm"
include "sylibr.mm"
include "simplrr.mm"
include "elind.mm"
include "simprl.mm"
include "simprr.mm"
include "ac6sfi.mm"
include "syl2anc.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "feq2.mm"
include "raleq.mm"
include "anbi12d.mm"
include "exbidv.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ex.mm"
include "sylan2b.mm"
include "rexlimdva.mm"
include "sylc.mm"

theorem cmpcovf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vf: setvar f
  let cJ: class J
  let cX: class X
  let vs: setvar s
  let vu: setvar u
  let vr: setvar r
  let cS: class S
  assume iscmp.1: |- X = U. J
  assume cmpcovf.2: |- ( z = ( f ` y ) -> ( ph <-> ps ) )

  disjoint f s
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint J s
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint f ph
  disjoint ph s
  disjoint ph x
  disjoint ps s
  disjoint ps z
  disjoint X x
  disjoint X s
  disjoint f u
  disjoint s u
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint r s
  disjoint r u
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint J r
  disjoint J u
  disjoint ph u
  disjoint ps u
  disjoint S r
  disjoint S s
  disjoint X r
  disjoint X u
  assert |- ( ( J e. Comp /\ A. x e. X E. y e. J ( x e. y /\ E. z e. A ph ) ) -> E. s e. ( ~P J i^i Fin ) ( X = U. s /\ E. f ( f : s --> A /\ A. y e. s ps ) ) )

  proof
    cJ
    ccmp
    wcel
    #
    vx
    cv
    vy
    cv
    wcel
    wph
    vz
    cA
    wrex
    #
    wa
    vy
    cJ
    wrex
    vx
    cX
    wral
    #
    wa
    @0
    cX
    vu
    cv
    #
    cuni
    #
    wceq
    #
    @1
    vy
    @3
    wral
    #
    wa
    #
    vu
    cJ
    cpw
    #
    cfn
    cin
    #
    wrex
    cX
    vs
    cv
    #
    cuni
    #
    wceq
    #
    @10
    cA
    vf
    cv
    #
    wf
    #
    wps
    vy
    @10
    wral
    #
    wa
    #
    vf
    wex
    #
    wa
    #
    vs
    @9
    wrex
    #
    @0
    @2
    simpl
    @1
    vx
    vy
    cJ
    cX
    vu
    iscmp.1
    cmpcov2
    @0
    @7
    @19
    vu
    @9
    @3
    @9
    wcel
    #
    @0
    @3
    cJ
    wss
    #
    @3
    cfn
    wcel
    #
    wa
    #
    @7
    @19
    wi
    @3
    cJ
    elfpw
    @0
    @23
    wa
    #
    @7
    @19
    @24
    @7
    wa
    #
    @20
    @5
    @3
    cA
    @13
    wf
    #
    wps
    vy
    @3
    wral
    #
    wa
    #
    vf
    wex
    #
    @19
    @25
    @8
    cfn
    @3
    @25
    @21
    @3
    @8
    wcel
    @0
    @21
    @22
    @7
    simplrl
    vu
    cJ
    selpw
    sylibr
    @0
    @21
    @22
    @7
    simplrr
    #
    elind
    @24
    @5
    @6
    simprl
    @25
    @22
    @6
    @29
    @30
    @24
    @5
    @6
    simprr
    wph
    wps
    vy
    vz
    @3
    cA
    vf
    cmpcovf.2
    ac6sfi
    syl2anc
    @18
    @5
    @29
    wa
    vs
    @3
    @9
    @10
    @3
    wceq
    #
    @12
    @5
    @17
    @29
    @31
    @11
    @4
    cX
    @10
    @3
    unieq
    eqeq2d
    @31
    @16
    @28
    vf
    @31
    @14
    @26
    @15
    @27
    @10
    @3
    cA
    @13
    feq2
    wps
    vy
    @10
    @3
    raleq
    anbi12d
    exbidv
    anbi12d
    rspcev
    syl12anc
    ex
    sylan2b
    rexlimdva
    sylc
end
