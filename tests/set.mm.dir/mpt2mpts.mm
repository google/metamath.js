include "cmpt2.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "csb.mm"
include "cmpt.mm"
include "mpt2mptsx.mm"
include "wceq.mm"
include "iunxpconst.mm"
include "mpteq1.mm"
include "ax-mp.mm"
include "eqtri.mm"

theorem mpt2mpts
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let vu: setvar u
  let vv: setvar v

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C z
  disjoint B x
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint B u
  disjoint B v
  disjoint C u
  disjoint C v
  assert |- ( x e. A , y e. B |-> C ) = ( z e. ( A X. B ) |-> [_ ( 1st ` z ) / x ]_ [_ ( 2nd ` z ) / y ]_ C )

  proof
    vx
    vy
    cA
    cB
    cC
    cmpt2
    vz
    vx
    cA
    vx
    cv
    csn
    cB
    cxp
    ciun
    #
    vx
    vz
    cv
    #
    c1st
    cfv
    vy
    @1
    c2nd
    cfv
    cC
    csb
    csb
    #
    cmpt
    #
    vz
    cA
    cB
    cxp
    #
    @2
    cmpt
    #
    vx
    vy
    vz
    cA
    cB
    cC
    mpt2mptsx
    @0
    @4
    wceq
    @3
    @5
    wceq
    vx
    cA
    cB
    iunxpconst
    vz
    @0
    @4
    @2
    mpteq1
    ax-mp
    eqtri
end
