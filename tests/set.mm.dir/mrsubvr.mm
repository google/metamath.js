include "wf.mm"
include "wss.mm"
include "wcel.mm"
include "w3a.mm"
include "cs1.mm"
include "cfv.mm"
include "cif.mm"
include "cmcn.mm"
include "cun.mm"
include "wceq.mm"
include "ssun2.mm"
include "simp2.mm"
include "simp3.mm"
include "sseldd.mm"
include "sseldi.mm"
include "eqid.mm"
include "mrsubcv.mm"
include "syld3an3.mm"
include "iftrue.mm"
include "3ad2ant3.mm"
include "eqtrd.mm"

theorem mrsubvr
  let cA: class A
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cV: class V
  let cX: class X
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vx: setvar x
  let cW: class W
  assume mrsubvr.v: |- V = ( mVR ` T )
  assume mrsubvr.r: |- R = ( mREx ` T )
  assume mrsubvr.s: |- S = ( mRSubst ` T )


  assert |- ( ( F : A --> R /\ A C_ V /\ X e. A ) -> ( ( S ` F ) ` <" X "> ) = ( F ` X ) )

  proof
    cA
    cR
    cF
    wf
    #
    cA
    cV
    wss
    #
    cX
    cA
    wcel
    #
    w3a
    #
    cX
    cs1
    #
    cF
    cS
    cfv
    cfv
    #
    @2
    cX
    cF
    cfv
    #
    @4
    cif
    #
    @6
    @0
    @1
    @2
    cX
    cT
    cmcn
    cfv
    #
    cV
    cun
    #
    wcel
    @5
    @7
    wceq
    @3
    cV
    @9
    cX
    cV
    @8
    ssun2
    @3
    cA
    cV
    cX
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    sseldd
    sseldi
    cA
    @8
    cR
    cS
    cT
    cF
    cV
    cX
    @8
    eqid
    mrsubvr.v
    mrsubvr.r
    mrsubvr.s
    mrsubcv
    syld3an3
    @2
    @0
    @7
    @6
    wceq
    @1
    @2
    @6
    @4
    iftrue
    3ad2ant3
    eqtrd
end
