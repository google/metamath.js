include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "cmulr.mm"
include "ctp.mm"
include "erngset-rN.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wceq.mm"
include "ctendo.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "eqid.mm"
include "rngplusg.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"

theorem erngfplus-rN
  let vt: setvar t
  let cD: class D
  let c.pl: class .+
  let cT: class T
  let vf: setvar f
  let cE: class E
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vk: setvar k
  let vw: setvar w
  assume erngset.h-r: |- H = ( LHyp ` K )
  assume erngset.t-r: |- T = ( ( LTrn ` K ) ` W )
  assume erngset.e-r: |- E = ( ( TEndo ` K ) ` W )
  assume erngset.d-r: |- D = ( ( EDRingR ` K ) ` W )
  assume erng.p-r: |- .+ = ( +g ` D )

  disjoint f s
  disjoint f t
  disjoint K f
  disjoint s t
  disjoint K s
  disjoint K t
  disjoint W f
  disjoint W s
  disjoint W t
  disjoint E s
  disjoint E t
  disjoint E k
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint f k
  disjoint f w
  disjoint k s
  disjoint k t
  disjoint K k
  disjoint s w
  disjoint t w
  disjoint K w
  disjoint T k
  disjoint E w
  disjoint T w
  disjoint W w
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
    cD
    cplusg
    cfv
    cnx
    cbs
    cfv
    cE
    cop
    cnx
    cplusg
    cfv
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
    #
    cfv
    @1
    vt
    cv
    #
    cfv
    ccom
    cmpt
    #
    cmpt2
    #
    cop
    cnx
    cmulr
    cfv
    vs
    vt
    cE
    cE
    @3
    @2
    ccom
    cmpt2
    #
    cop
    ctp
    #
    cplusg
    cfv
    #
    c.pl
    @5
    @0
    cD
    @7
    cplusg
    vt
    cD
    cT
    vf
    cE
    cH
    cK
    cV
    cW
    vs
    erngset.h-r
    erngset.t-r
    erngset.e-r
    erngset.d-r
    erngset-rN
    fveq2d
    erng.p-r
    @5
    cvv
    wcel
    @5
    @8
    wceq
    vs
    vt
    cE
    cE
    @4
    cE
    cW
    cK
    ctendo
    cfv
    #
    cfv
    cvv
    erngset.e-r
    cW
    @9
    fvex
    eqeltri
    #
    @10
    mpt2ex
    cE
    @5
    @7
    @6
    cvv
    @7
    eqid
    rngplusg
    ax-mp
    3eqtr4g
end
