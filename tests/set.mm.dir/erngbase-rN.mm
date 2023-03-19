include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cnx.mm"
include "cop.mm"
include "cplusg.mm"
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
include "eqid.mm"
include "rngbase.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"

theorem erngbase-rN
  let cC: class C
  let cD: class D
  let cT: class T
  let cE: class E
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vt: setvar t
  let vk: setvar k
  let vw: setvar w
  let vf: setvar f
  assume erngset.h-r: |- H = ( LHyp ` K )
  assume erngset.t-r: |- T = ( ( LTrn ` K ) ` W )
  assume erngset.e-r: |- E = ( ( TEndo ` K ) ` W )
  assume erngset.d-r: |- D = ( ( EDRingR ` K ) ` W )
  assume erng.c-r: |- C = ( Base ` D )


  assert |- ( ( K e. V /\ W e. H ) -> C = E )

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
    cbs
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
    @3
    @2
    ccom
    cmpt2
    #
    cop
    ctp
    #
    cbs
    cfv
    #
    cC
    cE
    @0
    cD
    @6
    cbs
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
    erng.c-r
    cE
    cvv
    wcel
    cE
    @7
    wceq
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
    @8
    fvex
    eqeltri
    cE
    @4
    @6
    @5
    cvv
    @6
    eqid
    rngbase
    ax-mp
    3eqtr4g
end
