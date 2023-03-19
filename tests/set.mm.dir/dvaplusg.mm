include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "ccom.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "dvafplusg.mm"
include "oveqd.mm"
include "eqid.mm"
include "tendopl.mm"
include "sylan9eq.mm"

theorem dvaplusg
  let c.pl: class .+
  let cR: class R
  let cS: class S
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
  let vt: setvar t
  let cG: class G
  let vg: setvar g
  assume dvafplus.h: |- H = ( LHyp ` K )
  assume dvafplus.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvafplus.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvafplus.u: |- U = ( ( DVecA ` K ) ` W )
  assume dvafplus.f: |- F = ( Scalar ` U )
  assume dvafplus.p: |- .+ = ( +g ` F )

  disjoint K f
  disjoint T f
  disjoint W f
  disjoint R f
  disjoint S f
  disjoint s t
  disjoint E s
  disjoint E t
  disjoint G f
  disjoint f g
  disjoint f s
  disjoint f t
  disjoint g s
  disjoint g t
  disjoint K g
  disjoint K s
  disjoint K t
  disjoint T g
  disjoint T s
  disjoint T t
  disjoint W g
  disjoint W s
  disjoint W t
  assert |- ( ( ( K e. V /\ W e. H ) /\ ( R e. E /\ S e. E ) ) -> ( R .+ S ) = ( f e. T |-> ( ( R ` f ) o. ( S ` f ) ) ) )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cR
    cE
    wcel
    cS
    cE
    wcel
    wa
    cR
    cS
    c.pl
    co
    cR
    cS
    vs
    vt
    cE
    cE
    vg
    cT
    vg
    cv
    #
    vs
    cv
    cfv
    @1
    vt
    cv
    cfv
    ccom
    cmpt
    cmpt2
    #
    co
    vf
    cT
    vf
    cv
    #
    cR
    cfv
    @3
    cS
    cfv
    ccom
    cmpt
    @0
    c.pl
    @2
    cR
    cS
    vt
    c.pl
    cT
    cU
    vg
    cE
    cF
    cH
    cK
    cV
    cW
    vs
    dvafplus.h
    dvafplus.t
    dvafplus.e
    dvafplus.u
    dvafplus.f
    dvafplus.p
    dvafplusg
    oveqd
    vt
    @2
    cT
    cR
    vg
    vf
    cE
    cK
    cS
    cW
    vs
    @2
    eqid
    dvafplus.t
    tendopl
    sylan9eq
end
