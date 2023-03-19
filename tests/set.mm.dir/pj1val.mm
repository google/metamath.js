include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "crio.mm"
include "cvv.mm"
include "cmpt.mm"
include "pj1fval.mm"
include "adantr.mm"
include "simpr.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "riotabidv.mm"
include "riotaex.mm"
include "a1i.mm"
include "fvmptd.mm"

theorem pj1val
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cP: class P
  let c.pl: class .+
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  let cV: class V
  let cX: class X
  let vg: setvar g
  let vt: setvar t
  let vu: setvar u
  let vz: setvar z
  assume pj1fval.v: |- B = ( Base ` G )
  assume pj1fval.a: |- .+ = ( +g ` G )
  assume pj1fval.s: |- .(+) = ( LSSum ` G )
  assume pj1fval.p: |- P = ( proj1 ` G )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint T x
  disjoint T y
  disjoint U x
  disjoint U y
  disjoint .(+) x
  disjoint .(+) y
  disjoint G x
  disjoint G y
  disjoint V x
  disjoint V y
  disjoint X x
  disjoint X y
  disjoint g t
  disjoint g u
  disjoint g z
  disjoint .+ g
  disjoint t u
  disjoint t z
  disjoint .+ t
  disjoint u z
  disjoint .+ u
  disjoint .+ z
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint t x
  disjoint t y
  disjoint B t
  disjoint u x
  disjoint u y
  disjoint B u
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint T t
  disjoint T u
  disjoint T z
  disjoint U t
  disjoint U u
  disjoint U z
  disjoint .(+) g
  disjoint .(+) t
  disjoint .(+) u
  disjoint .(+) z
  disjoint G g
  disjoint G t
  disjoint G u
  disjoint G z
  disjoint V t
  disjoint V u
  disjoint V z
  disjoint X z
  assert |- ( ( ( G e. V /\ T C_ B /\ U C_ B ) /\ X e. ( T .(+) U ) ) -> ( ( T P U ) ` X ) = ( iota_ x e. T E. y e. U X = ( x .+ y ) ) )

  proof
    cG
    cV
    wcel
    cT
    cB
    wss
    cU
    cB
    wss
    w3a
    #
    cX
    cT
    cU
    c.po
    co
    #
    wcel
    #
    wa
    #
    vz
    cX
    vz
    cv
    #
    vx
    cv
    vy
    cv
    c.pl
    co
    #
    wceq
    #
    vy
    cU
    wrex
    #
    vx
    cT
    crio
    #
    cX
    @5
    wceq
    #
    vy
    cU
    wrex
    #
    vx
    cT
    crio
    #
    @1
    cT
    cU
    cP
    co
    #
    cvv
    @0
    @12
    vz
    @1
    @8
    cmpt
    wceq
    @2
    vx
    vy
    vz
    cB
    cP
    c.pl
    c.po
    cT
    cU
    cG
    cV
    pj1fval.v
    pj1fval.a
    pj1fval.s
    pj1fval.p
    pj1fval
    adantr
    @3
    @4
    cX
    wceq
    #
    wa
    #
    @7
    @10
    vx
    cT
    @14
    @6
    @9
    vy
    cU
    @14
    @4
    cX
    @5
    @3
    @13
    simpr
    eqeq1d
    rexbidv
    riotabidv
    @0
    @2
    simpr
    @11
    cvv
    wcel
    @3
    @10
    vx
    cT
    riotaex
    a1i
    fvmptd
end
