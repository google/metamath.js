include "wcel.mm"
include "wa.mm"
include "cmulr.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cplusg.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "ctp.mm"
include "erngset.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wceq.mm"
include "ctendo.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "eqid.mm"
include "rngmulr.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"

theorem erngfmul
  let vt: setvar t
  let cD: class D
  let cT: class T
  let c.x: class .x.
  let cE: class E
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vk: setvar k
  let vw: setvar w
  let vf: setvar f
  assume erngset.h: |- H = ( LHyp ` K )
  assume erngset.t: |- T = ( ( LTrn ` K ) ` W )
  assume erngset.e: |- E = ( ( TEndo ` K ) ` W )
  assume erngset.d: |- D = ( ( EDRing ` K ) ` W )
  assume erng.m: |- .x. = ( .r ` D )

  disjoint s t
  disjoint K s
  disjoint K t
  disjoint W s
  disjoint W t
  disjoint E s
  disjoint E t
  disjoint E k
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint f k
  disjoint f s
  disjoint f t
  disjoint f w
  disjoint K f
  disjoint k s
  disjoint k t
  disjoint K k
  disjoint s w
  disjoint t w
  disjoint K w
  disjoint T k
  disjoint E w
  disjoint T w
  disjoint W f
  disjoint W w
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
    cD
    cmulr
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
    @2
    @3
    ccom
    #
    cmpt2
    #
    cop
    ctp
    #
    cmulr
    cfv
    #
    c.x
    @6
    @0
    cD
    @7
    cmulr
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
    erngset.h
    erngset.t
    erngset.e
    erngset.d
    erngset
    fveq2d
    erng.m
    @6
    cvv
    wcel
    @6
    @8
    wceq
    vs
    vt
    cE
    cE
    @5
    cE
    cW
    cK
    ctendo
    cfv
    #
    cfv
    cvv
    erngset.e
    cW
    @9
    fvex
    eqeltri
    #
    @10
    mpt2ex
    cE
    @4
    @7
    @6
    cvv
    @7
    eqid
    rngmulr
    ax-mp
    3eqtr4g
end
