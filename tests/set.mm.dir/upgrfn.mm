include "cupgr.mm"
include "wcel.mm"
include "wfn.mm"
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
include "cdm.mm"
include "upgrf.mm"
include "fndm.mm"
include "feq2d.mm"
include "syl5ibcom.mm"
include "imp.mm"

theorem upgrfn
  let vx: setvar x
  let cA: class A
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
  assert |- ( ( G e. UPGraph /\ E Fn A ) -> E : A --> { x e. ( ~P V \ { (/) } ) | ( # ` x ) <_ 2 } )

  proof
    cG
    cupgr
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
    cle
    wbr
    vx
    cV
    cpw
    c0
    csn
    cdif
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
    isupgr.v
    isupgr.e
    upgrf
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
