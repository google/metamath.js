include "cmpl.mm"
include "co.mm"
include "cress.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cv.mm"
include "cmps.mm"
include "c0g.mm"
include "cfv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cbs.mm"
include "crab.mm"
include "csb.mm"
include "ovexd.mm"
include "id.mm"
include "oveq12.mm"
include "sylan9eqr.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "simplr.mm"
include "breq2d.mm"
include "rabeqbidv.mm"
include "oveq12d.mm"
include "csbied.mm"
include "df-mpl.mm"
include "ovex.mm"
include "ovmpt2a.mm"
include "wn.mm"
include "c0.mm"
include "reldmmpl.mm"
include "ovprc.mm"
include "ress0.mm"
include "reldmpsr.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem mplval
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cU: class U
  let vf: setvar f
  let cI: class I
  let c.0: class .0.
  let vi: setvar i
  let vr: setvar r
  let vs: setvar s
  let cX: class X
  assume mplval.p: |- P = ( I mPoly R )
  assume mplval.s: |- S = ( I mPwSer R )
  assume mplval.b: |- B = ( Base ` S )
  assume mplval.z: |- .0. = ( 0g ` R )
  assume mplval.u: |- U = { f e. B | f finSupp .0. }

  disjoint B f
  disjoint I f
  disjoint R f
  disjoint .0. f
  disjoint f i
  disjoint f r
  disjoint f s
  disjoint i r
  disjoint i s
  disjoint I i
  disjoint r s
  disjoint I r
  disjoint I s
  disjoint R i
  disjoint R r
  disjoint R s
  disjoint S i
  disjoint S r
  disjoint S s
  disjoint U i
  disjoint U r
  disjoint U s
  disjoint X f
  assert |- P = ( S |`s U )

  proof
    cP
    cI
    cR
    cmpl
    co
    #
    cS
    cU
    cress
    co
    #
    mplval.p
    cI
    cvv
    wcel
    cR
    cvv
    wcel
    wa
    #
    @0
    @1
    wceq
    vi
    vr
    cI
    cR
    cvv
    cvv
    vs
    vi
    cv
    #
    vr
    cv
    #
    cmps
    co
    #
    vs
    cv
    #
    vf
    cv
    #
    @4
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    vf
    @6
    cbs
    cfv
    #
    crab
    #
    cress
    co
    #
    csb
    @1
    cmpl
    @3
    cI
    wceq
    #
    @4
    cR
    wceq
    #
    wa
    #
    vs
    @5
    @12
    @1
    cvv
    @15
    @3
    @4
    cmps
    ovexd
    @15
    @6
    @5
    wceq
    #
    wa
    #
    @6
    cS
    @11
    cU
    cress
    @17
    @6
    cI
    cR
    cmps
    co
    #
    cS
    @16
    @15
    @6
    @5
    @18
    @16
    id
    @3
    cI
    @4
    cR
    cmps
    oveq12
    sylan9eqr
    mplval.s
    syl6eqr
    #
    @17
    @11
    @7
    c.0
    cfsupp
    wbr
    #
    vf
    cB
    crab
    cU
    @17
    @9
    @20
    vf
    @10
    cB
    @17
    @10
    cS
    cbs
    cfv
    cB
    @17
    @6
    cS
    cbs
    @19
    fveq2d
    mplval.b
    syl6eqr
    @17
    @8
    c.0
    @7
    cfsupp
    @17
    @8
    cR
    c0g
    cfv
    c.0
    @17
    @4
    cR
    c0g
    @13
    @14
    @16
    simplr
    fveq2d
    mplval.z
    syl6eqr
    breq2d
    rabeqbidv
    mplval.u
    syl6eqr
    oveq12d
    csbied
    vs
    vf
    vi
    vr
    df-mpl
    cS
    cU
    cress
    ovex
    ovmpt2a
    @2
    wn
    #
    @0
    c0
    cU
    cress
    co
    #
    @1
    @21
    @0
    c0
    @22
    cI
    cR
    cmpl
    reldmmpl
    ovprc
    cU
    ress0
    syl6eqr
    @21
    cS
    c0
    cU
    cress
    @21
    cS
    @18
    c0
    mplval.s
    cI
    cR
    cmps
    reldmpsr
    ovprc
    syl5eq
    oveq1d
    eqtr4d
    pm2.61i
    eqtri
end
