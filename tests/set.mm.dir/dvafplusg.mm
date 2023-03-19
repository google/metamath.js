include "wcel.mm"
include "wa.mm"
include "cedring.mm"
include "cfv.mm"
include "cplusg.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "eqid.mm"
include "dvasca.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "erngfplus.mm"
include "eqtrd.mm"

theorem dvafplusg
  let vt: setvar t
  let c.pl: class .+
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vs: setvar s
  let cG: class G
  let vg: setvar g
  let cR: class R
  let cS: class S
  assume dvafplus.h: |- H = ( LHyp ` K )
  assume dvafplus.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvafplus.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvafplus.u: |- U = ( ( DVecA ` K ) ` W )
  assume dvafplus.f: |- F = ( Scalar ` U )
  assume dvafplus.p: |- .+ = ( +g ` F )

  disjoint s t
  disjoint E s
  disjoint E t
  disjoint f s
  disjoint f t
  disjoint K f
  disjoint K s
  disjoint K t
  disjoint T f
  disjoint T s
  disjoint T t
  disjoint W f
  disjoint W s
  disjoint W t
  disjoint G f
  disjoint f g
  disjoint g s
  disjoint g t
  disjoint K g
  disjoint T g
  disjoint W g
  disjoint R f
  disjoint S f
  assert |- ( ( K e. V /\ W e. H ) -> .+ = ( s e. E , t e. E |-> ( f e. T |-> ( ( s ` f ) o. ( t ` f ) ) ) ) )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    c.pl
    cW
    cK
    cedring
    cfv
    cfv
    #
    cplusg
    cfv
    #
    vs
    vt
    cE
    cE
    vf
    cT
    vf
    cv
    #
    vs
    cv
    cfv
    @3
    vt
    cv
    cfv
    ccom
    cmpt
    cmpt2
    @0
    c.pl
    cF
    cplusg
    cfv
    @2
    dvafplus.p
    @0
    cF
    @1
    cplusg
    @1
    cU
    cF
    cH
    cK
    cW
    cV
    dvafplus.h
    @1
    eqid
    #
    dvafplus.u
    dvafplus.f
    dvasca
    fveq2d
    syl5eq
    vt
    @1
    @2
    cT
    vf
    cE
    cH
    cK
    cV
    cW
    vs
    dvafplus.h
    dvafplus.t
    dvafplus.e
    @4
    @2
    eqid
    erngfplus
    eqtrd
end
