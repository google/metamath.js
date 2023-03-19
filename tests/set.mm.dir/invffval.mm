include "cinv.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "ccnv.mm"
include "cin.mm"
include "cmpt2.mm"
include "ccat.mm"
include "wcel.mm"
include "wceq.mm"
include "cbs.mm"
include "csect.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "cnveqd.mm"
include "ineq12d.mm"
include "mpt2eq123dv.mm"
include "df-inv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"

theorem invffval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cS: class S
  let cN: class N
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vz: setvar z
  assume invfval.b: |- B = ( Base ` C )
  assume invfval.n: |- N = ( Inv ` C )
  assume invfval.c: |- ( ph -> C e. Cat )
  assume invfval.x: |- ( ph -> X e. B )
  assume invfval.y: |- ( ph -> Y e. B )
  assume invfval.s: |- S = ( Sect ` C )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint C x
  disjoint C y
  disjoint S x
  disjoint S y
  disjoint c x
  disjoint c y
  disjoint B c
  disjoint f g
  disjoint f h
  disjoint f x
  disjoint f y
  disjoint f ph
  disjoint g h
  disjoint g x
  disjoint g y
  disjoint g ph
  disjoint h x
  disjoint h y
  disjoint h ph
  disjoint f z
  disjoint X f
  disjoint g z
  disjoint X g
  disjoint h z
  disjoint X h
  disjoint x z
  disjoint y z
  disjoint X z
  disjoint Y f
  disjoint Y g
  disjoint Y h
  disjoint Y z
  disjoint C c
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c z
  disjoint N c
  disjoint N f
  disjoint N g
  disjoint N h
  disjoint N z
  disjoint S c
  assert |- ( ph -> N = ( x e. B , y e. B |-> ( ( x S y ) i^i `' ( y S x ) ) ) )

  proof
    wph
    cN
    cC
    cinv
    cfv
    #
    vx
    vy
    cB
    cB
    vx
    cv
    #
    vy
    cv
    #
    cS
    co
    #
    @2
    @1
    cS
    co
    #
    ccnv
    #
    cin
    #
    cmpt2
    #
    invfval.n
    wph
    cC
    ccat
    wcel
    @0
    @7
    wceq
    invfval.c
    vc
    cC
    vx
    vy
    vc
    cv
    #
    cbs
    cfv
    #
    @9
    @1
    @2
    @8
    csect
    cfv
    #
    co
    #
    @2
    @1
    @10
    co
    #
    ccnv
    #
    cin
    #
    cmpt2
    @7
    ccat
    cinv
    @8
    cC
    wceq
    #
    vx
    vy
    @9
    @9
    @14
    cB
    cB
    @6
    @15
    @9
    cC
    cbs
    cfv
    #
    cB
    @8
    cC
    cbs
    fveq2
    invfval.b
    syl6eqr
    #
    @17
    @15
    @11
    @3
    @13
    @5
    @15
    @10
    cS
    @1
    @2
    @15
    @10
    cC
    csect
    cfv
    cS
    @8
    cC
    csect
    fveq2
    invfval.s
    syl6eqr
    #
    oveqd
    @15
    @12
    @4
    @15
    @10
    cS
    @2
    @1
    @18
    oveqd
    cnveqd
    ineq12d
    mpt2eq123dv
    vx
    vy
    vc
    df-inv
    vx
    vy
    cB
    cB
    @6
    cB
    @16
    cvv
    invfval.b
    cC
    cbs
    fvex
    eqeltri
    #
    @19
    mpt2ex
    fvmpt
    syl
    syl5eq
end
