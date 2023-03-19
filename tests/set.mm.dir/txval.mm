include "wcel.mm"
include "cvv.mm"
include "ctx.mm"
include "co.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "elex.mm"
include "cv.mm"
include "cxp.mm"
include "cmpt2.mm"
include "crn.mm"
include "wa.mm"
include "mpt2eq12.mm"
include "rneqd.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "df-tx.mm"
include "fvex.mm"
include "ovmpt2a.mm"
include "syl2an.mm"

theorem txval
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cS: class S
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vp: setvar p
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let vw: setvar w
  let cX: class X
  let cY: class Y
  assume txval.1: |- B = ran ( x e. R , y e. S |-> ( x X. y ) )

  disjoint x y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a p
  disjoint a r
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint R a
  disjoint b c
  disjoint b d
  disjoint b p
  disjoint b r
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint R b
  disjoint c d
  disjoint c p
  disjoint c r
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint R c
  disjoint d p
  disjoint d r
  disjoint d s
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint R d
  disjoint p r
  disjoint p s
  disjoint p t
  disjoint p u
  disjoint p v
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint R p
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint R r
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint R s
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint R t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint R u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint R v
  disjoint x z
  disjoint y z
  disjoint R z
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S p
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S z
  disjoint a w
  disjoint B a
  disjoint b w
  disjoint B b
  disjoint c w
  disjoint B c
  disjoint d w
  disjoint B d
  disjoint p w
  disjoint B p
  disjoint r w
  disjoint B r
  disjoint s w
  disjoint B s
  disjoint t w
  disjoint B t
  disjoint u w
  disjoint B u
  disjoint v w
  disjoint B v
  disjoint w z
  disjoint B w
  disjoint B z
  disjoint w x
  disjoint w y
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  assert |- ( ( R e. V /\ S e. W ) -> ( R tX S ) = ( topGen ` B ) )

  proof
    cR
    cV
    wcel
    cR
    cvv
    wcel
    cS
    cvv
    wcel
    cR
    cS
    ctx
    co
    cB
    ctg
    cfv
    #
    wceq
    cS
    cW
    wcel
    cR
    cV
    elex
    cS
    cW
    elex
    vr
    vs
    cR
    cS
    cvv
    cvv
    vx
    vy
    vr
    cv
    #
    vs
    cv
    #
    vx
    cv
    vy
    cv
    cxp
    #
    cmpt2
    #
    crn
    #
    ctg
    cfv
    @0
    ctx
    @1
    cR
    wceq
    @2
    cS
    wceq
    wa
    #
    @5
    cB
    ctg
    @6
    @5
    vx
    vy
    cR
    cS
    @3
    cmpt2
    #
    crn
    cB
    @6
    @4
    @7
    vx
    vy
    @1
    @2
    cR
    cS
    @3
    mpt2eq12
    rneqd
    txval.1
    syl6eqr
    fveq2d
    vx
    vy
    vs
    vr
    df-tx
    cB
    ctg
    fvex
    ovmpt2a
    syl2an
end
