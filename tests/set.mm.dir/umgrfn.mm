include "cumgr.mm"
include "wcel.mm"
include "wfn.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "wf.mm"
include "cdm.mm"
include "umgrf.mm"
include "fndm.mm"
include "feq2d.mm"
include "syl5ibcom.mm"
include "imp.mm"

theorem umgrfn
  let vx: setvar x
  let cA: class A
  let cE: class E
  let cG: class G
  let cV: class V
  let ve: setvar e
  let vg: setvar g
  let vh: setvar h
  let vv: setvar v
  assume isumgr.v: |- V = ( Vtx ` G )
  assume isumgr.e: |- E = ( iEdg ` G )

  disjoint G x
  disjoint V x
  disjoint e g
  disjoint e h
  disjoint e v
  disjoint e x
  disjoint g h
  disjoint g v
  disjoint g x
  disjoint h v
  disjoint h x
  disjoint v x
  disjoint E h
  disjoint G h
  disjoint V h
  assert |- ( ( G e. UMGraph /\ E Fn A ) -> E : A --> { x e. ~P V | ( # ` x ) = 2 } )

  proof
    cG
    cumgr
    wcel
    #
    cE
    cA
    wfn
    #
    cA
    vx
    cv
    chash
    cfv
    c2
    wceq
    vx
    cV
    cpw
    crab
    #
    cE
    wf
    #
    @0
    cE
    cdm
    #
    @2
    cE
    wf
    @1
    @3
    vx
    cE
    cG
    cV
    isumgr.v
    isumgr.e
    umgrf
    @1
    @4
    cA
    @2
    cE
    cA
    cE
    fndm
    feq2d
    syl5ibcom
    imp
end
