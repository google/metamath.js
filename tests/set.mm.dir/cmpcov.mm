include "ccmp.mm"
include "wcel.mm"
include "wss.mm"
include "cuni.mm"
include "wceq.mm"
include "cv.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "pweq.mm"
include "ineq1d.mm"
include "rexeqdv.mm"
include "imbi12d.mm"
include "wral.mm"
include "ctop.mm"
include "iscmp.mm"
include "simprbi.mm"
include "adantr.mm"
include "simpr.mm"
include "cvv.mm"
include "wb.mm"
include "ssexg.mm"
include "ancoms.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbird.mm"
include "rspcdva.mm"
include "3impia.mm"

theorem cmpcov
  let cS: class S
  let cJ: class J
  let cX: class X
  let vs: setvar s
  let vf: setvar f
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vr: setvar r
  let wph: wff ph
  let wps: wff ps
  assume iscmp.1: |- X = U. J

  disjoint J s
  disjoint S s
  disjoint f s
  disjoint f u
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint s u
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint x y
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
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint f ph
  disjoint ph s
  disjoint ph u
  disjoint ph x
  disjoint ps s
  disjoint ps u
  disjoint ps z
  disjoint S r
  disjoint X r
  disjoint X u
  disjoint X x
  assert |- ( ( J e. Comp /\ S C_ J /\ X = U. S ) -> E. s e. ( ~P S i^i Fin ) X = U. s )

  proof
    cJ
    ccmp
    wcel
    #
    cS
    cJ
    wss
    #
    cX
    cS
    cuni
    #
    wceq
    #
    cX
    vs
    cv
    cuni
    wceq
    #
    vs
    cS
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @0
    @1
    wa
    #
    cX
    vr
    cv
    #
    cuni
    #
    wceq
    #
    @4
    vs
    @9
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    #
    @3
    @7
    wi
    vr
    cJ
    cpw
    #
    cS
    @9
    cS
    wceq
    #
    @11
    @3
    @14
    @7
    @17
    @10
    @2
    cX
    @9
    cS
    unieq
    eqeq2d
    @17
    @4
    vs
    @13
    @6
    @17
    @12
    @5
    cfn
    @9
    cS
    pweq
    ineq1d
    rexeqdv
    imbi12d
    @0
    @15
    vr
    @16
    wral
    #
    @1
    @0
    cJ
    ctop
    wcel
    @18
    vr
    vs
    cJ
    cX
    iscmp.1
    iscmp
    simprbi
    adantr
    @8
    cS
    @16
    wcel
    #
    @1
    @0
    @1
    simpr
    @8
    cS
    cvv
    wcel
    #
    @19
    @1
    wb
    @1
    @0
    @20
    cS
    cJ
    ccmp
    ssexg
    ancoms
    cS
    cJ
    cvv
    elpwg
    syl
    mpbird
    rspcdva
    3impia
end
