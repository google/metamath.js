include "cumgr.mm"
include "wcel.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "wf.mm"
include "isumgrs.mm"
include "ibi.mm"

theorem umgrf
  let vx: setvar x
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
  assert |- ( G e. UMGraph -> E : dom E --> { x e. ~P V | ( # ` x ) = 2 } )

  proof
    cG
    cumgr
    wcel
    cE
    cdm
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
    cE
    wf
    vx
    cumgr
    cE
    cG
    cV
    isumgr.v
    isumgr.e
    isumgrs
    ibi
end
