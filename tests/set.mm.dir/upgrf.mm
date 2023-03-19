include "cupgr.mm"
include "wcel.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wf.mm"
include "isupgr.mm"
include "ibi.mm"

theorem upgrf
  let vx: setvar x
  let cE: class E
  let cG: class G
  let cV: class V
  let ve: setvar e
  let vg: setvar g
  let vh: setvar h
  let vv: setvar v
  assume isupgr.v: |- V = ( Vtx ` G )
  assume isupgr.e: |- E = ( iEdg ` G )

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
  assert |- ( G e. UPGraph -> E : dom E --> { x e. ( ~P V \ { (/) } ) | ( # ` x ) <_ 2 } )

  proof
    cG
    cupgr
    wcel
    cE
    cdm
    vx
    cv
    chash
    cfv
    c2
    cle
    wbr
    vx
    cV
    cpw
    c0
    csn
    cdif
    crab
    cE
    wf
    vx
    cupgr
    cE
    cG
    cV
    isupgr.v
    isupgr.e
    isupgr
    ibi
end
