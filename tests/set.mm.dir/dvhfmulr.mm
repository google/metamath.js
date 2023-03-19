include "wcel.mm"
include "wa.mm"
include "cedring.mm"
include "cfv.mm"
include "cmulr.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt2.mm"
include "eqid.mm"
include "dvhsca.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "erngfmul.mm"
include "eqtrd.mm"

theorem dvhfmulr
  let vt: setvar t
  let cT: class T
  let c.x: class .x.
  let cU: class U
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vs: setvar s
  assume dvhfmul.h: |- H = ( LHyp ` K )
  assume dvhfmul.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvhfmul.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvhfmul.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvhfmul.f: |- F = ( Scalar ` U )
  assume dvhfmul.m: |- .x. = ( .r ` F )

  disjoint s t
  disjoint E s
  disjoint E t
  disjoint K s
  disjoint K t
  disjoint W s
  disjoint W t
  assert |- ( ( K e. V /\ W e. H ) -> .x. = ( s e. E , t e. E |-> ( s o. t ) ) )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    c.x
    cW
    cK
    cedring
    cfv
    cfv
    #
    cmulr
    cfv
    #
    vs
    vt
    cE
    cE
    vs
    cv
    vt
    cv
    ccom
    cmpt2
    @0
    c.x
    cF
    cmulr
    cfv
    @2
    dvhfmul.m
    @0
    cF
    @1
    cmulr
    @1
    cU
    cF
    cH
    cK
    cW
    cV
    dvhfmul.h
    @1
    eqid
    #
    dvhfmul.u
    dvhfmul.f
    dvhsca
    fveq2d
    syl5eq
    vt
    @1
    cT
    @2
    cE
    cH
    cK
    cV
    cW
    vs
    dvhfmul.h
    dvhfmul.t
    dvhfmul.e
    @3
    @2
    eqid
    erngfmul
    eqtrd
end
