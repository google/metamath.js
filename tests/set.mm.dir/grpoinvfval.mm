include "cgr.mm"
include "wcel.mm"
include "cgn.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "crio.mm"
include "cmpt.mm"
include "cvv.mm"
include "crn.mm"
include "rnexg.mm"
include "syl5eqel.mm"
include "mptexg.mm"
include "syl.mm"
include "cgi.mm"
include "rneq.mm"
include "syl6eqr.mm"
include "oveq.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "riotaeqbidv.mm"
include "mpteq12dv.mm"
include "df-ginv.mm"
include "fvmptg.mm"
include "mpdan.mm"
include "syl5eq.mm"

theorem grpoinvfval
  let vx: setvar x
  let vy: setvar y
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  let cA: class A
  let vg: setvar g
  assume grpinvfval.1: |- X = ran G
  assume grpinvfval.2: |- U = ( GId ` G )
  assume grpinvfval.3: |- N = ( inv ` G )

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint X x
  disjoint X y
  disjoint U x
  disjoint A x
  disjoint A y
  disjoint g x
  disjoint g y
  disjoint G g
  disjoint X g
  disjoint U g
  assert |- ( G e. GrpOp -> N = ( x e. X |-> ( iota_ y e. X ( y G x ) = U ) ) )

  proof
    cG
    cgr
    wcel
    #
    cN
    cG
    cgn
    cfv
    #
    vx
    cX
    vy
    cv
    #
    vx
    cv
    #
    cG
    co
    #
    cU
    wceq
    #
    vy
    cX
    crio
    #
    cmpt
    #
    grpinvfval.3
    @0
    @7
    cvv
    wcel
    #
    @1
    @7
    wceq
    @0
    cX
    cvv
    wcel
    @8
    @0
    cX
    cG
    crn
    #
    cvv
    grpinvfval.1
    cG
    cgr
    rnexg
    syl5eqel
    vx
    cX
    @6
    cvv
    mptexg
    syl
    vg
    cG
    vx
    vg
    cv
    #
    crn
    #
    @2
    @3
    @10
    co
    #
    @10
    cgi
    cfv
    #
    wceq
    #
    vy
    @11
    crio
    #
    cmpt
    @7
    cgr
    cvv
    cgn
    @10
    cG
    wceq
    #
    vx
    @11
    @15
    cX
    @6
    @16
    @11
    @9
    cX
    @10
    cG
    rneq
    grpinvfval.1
    syl6eqr
    #
    @16
    @14
    @5
    vy
    @11
    cX
    @17
    @16
    @12
    @4
    @13
    cU
    @2
    @3
    @10
    cG
    oveq
    @16
    @13
    cG
    cgi
    cfv
    cU
    @10
    cG
    cgi
    fveq2
    grpinvfval.2
    syl6eqr
    eqeq12d
    riotaeqbidv
    mpteq12dv
    vx
    vy
    vg
    df-ginv
    fvmptg
    mpdan
    syl5eq
end
