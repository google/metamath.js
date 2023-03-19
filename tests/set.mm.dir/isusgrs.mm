include "wcel.mm"
include "cusgr.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wf1.mm"
include "isusgr.mm"
include "wb.mm"
include "prprrab.mm"
include "f1eq3.mm"
include "mp1i.mm"
include "bitrd.mm"

theorem isusgrs
  let vx: setvar x
  let cU: class U
  let cE: class E
  let cG: class G
  let cV: class V
  let ve: setvar e
  let vg: setvar g
  let vh: setvar h
  let vv: setvar v
  assume isuspgr.v: |- V = ( Vtx ` G )
  assume isuspgr.e: |- E = ( iEdg ` G )

  disjoint G x
  disjoint V x
  disjoint U x
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
  assert |- ( G e. U -> ( G e. USGraph <-> E : dom E -1-1-> { x e. ~P V | ( # ` x ) = 2 } ) )

  proof
    cG
    cU
    wcel
    #
    cG
    cusgr
    wcel
    cE
    cdm
    #
    vx
    cv
    chash
    cfv
    c2
    wceq
    #
    vx
    cV
    cpw
    #
    c0
    csn
    cdif
    crab
    #
    cE
    wf1
    #
    @1
    @2
    vx
    @3
    crab
    #
    cE
    wf1
    #
    vx
    cU
    cE
    cG
    cV
    isuspgr.v
    isuspgr.e
    isusgr
    @4
    @6
    wceq
    @5
    @7
    wb
    @0
    vx
    cV
    prprrab
    @4
    @6
    @1
    cE
    f1eq3
    mp1i
    bitrd
end
