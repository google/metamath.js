include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "ctop.mm"
include "ccmp.mm"
include "pweq.mm"
include "unieq.mm"
include "syl6eqr.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "raleqbidv.mm"
include "df-cmp.mm"
include "elrab2.mm"

theorem iscmp
  let vy: setvar y
  let vz: setvar z
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vs: setvar s
  let vu: setvar u
  let vx: setvar x
  let cA: class A
  let vr: setvar r
  let wph: wff ph
  let wps: wff ps
  let cS: class S
  assume iscmp.1: |- X = U. J

  disjoint y z
  disjoint J y
  disjoint J z
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
  disjoint A y
  disjoint A z
  disjoint r s
  disjoint r u
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint J r
  disjoint J s
  disjoint J u
  disjoint J x
  disjoint f ph
  disjoint ph s
  disjoint ph u
  disjoint ph x
  disjoint ps s
  disjoint ps u
  disjoint ps z
  disjoint S r
  disjoint S s
  disjoint X r
  disjoint X u
  disjoint X x
  assert |- ( J e. Comp <-> ( J e. Top /\ A. y e. ~P J ( X = U. y -> E. z e. ( ~P y i^i Fin ) X = U. z ) ) )

  proof
    vx
    cv
    #
    cuni
    #
    vy
    cv
    #
    cuni
    #
    wceq
    #
    @1
    vz
    cv
    cuni
    #
    wceq
    #
    vz
    @2
    cpw
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vy
    @0
    cpw
    #
    wral
    cX
    @3
    wceq
    #
    cX
    @5
    wceq
    #
    vz
    @7
    wrex
    #
    wi
    #
    vy
    cJ
    cpw
    #
    wral
    vx
    cJ
    ctop
    ccmp
    @0
    cJ
    wceq
    #
    @9
    @14
    vy
    @10
    @15
    @0
    cJ
    pweq
    @16
    @4
    @11
    @8
    @13
    @16
    @1
    cX
    @3
    @16
    @1
    cJ
    cuni
    cX
    @0
    cJ
    unieq
    iscmp.1
    syl6eqr
    #
    eqeq1d
    @16
    @6
    @12
    vz
    @7
    @16
    @1
    cX
    @5
    @17
    eqeq1d
    rexbidv
    imbi12d
    raleqbidv
    vx
    vy
    vz
    df-cmp
    elrab2
end
