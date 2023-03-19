include "wcel.mm"
include "cumgr.mm"
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
include "wf.mm"
include "isumgr.mm"
include "prprrab.mm"
include "a1i.mm"
include "feq3d.mm"
include "bitrd.mm"

theorem isumgrs
  let vx: setvar x
  let cU: class U
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
  assert |- ( G e. U -> ( G e. UMGraph <-> E : dom E --> { x e. ~P V | ( # ` x ) = 2 } ) )

  proof
    cG
    cU
    wcel
    #
    cG
    cumgr
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
    wf
    @1
    @2
    vx
    @3
    crab
    #
    cE
    wf
    vx
    cU
    cE
    cG
    cV
    isumgr.v
    isumgr.e
    isumgr
    @0
    @4
    @5
    cE
    @1
    @4
    @5
    wceq
    @0
    vx
    cV
    prprrab
    a1i
    feq3d
    bitrd
end
