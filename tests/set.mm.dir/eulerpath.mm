include "ceupth.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "cupgr.mm"
include "wcel.mm"
include "c2.mm"
include "cv.mm"
include "cvtxdg.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "chash.mm"
include "cc0.mm"
include "cpr.mm"
include "cdm.mm"
include "wex.mm"
include "wi.mm"
include "wrel.mm"
include "wceq.mm"
include "wb.mm"
include "releupth.mm"
include "reldm0.mm"
include "ax-mp.mm"
include "necon3bii.mm"
include "n0.mm"
include "bitri.mm"
include "vex.mm"
include "eldm.mm"
include "eulerpathpr.mm"
include "expcom.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "impcom.mm"

theorem eulerpath
  let vx: setvar x
  let cG: class G
  let cV: class V
  let cF: class F
  let cP: class P
  let vf: setvar f
  let vp: setvar p
  assume eulerpathpr.v: |- V = ( Vtx ` G )

  disjoint G x
  disjoint V x
  disjoint F x
  disjoint P x
  disjoint G f
  disjoint G p
  disjoint f p
  disjoint V f
  disjoint V p
  disjoint f x
  disjoint p x
  assert |- ( ( G e. UPGraph /\ ( EulerPaths ` G ) =/= (/) ) -> ( # ` { x e. V | -. 2 || ( ( VtxDeg ` G ) ` x ) } ) e. { 0 , 2 } )

  proof
    cG
    ceupth
    cfv
    #
    c0
    wne
    #
    cG
    cupgr
    wcel
    #
    c2
    vx
    cv
    cG
    cvtxdg
    cfv
    cfv
    cdvds
    wbr
    wn
    vx
    cV
    crab
    chash
    cfv
    cc0
    c2
    cpr
    wcel
    #
    @1
    vf
    cv
    #
    @0
    cdm
    #
    wcel
    #
    vf
    wex
    #
    @2
    @3
    wi
    #
    @1
    @5
    c0
    wne
    @7
    @0
    c0
    @5
    c0
    @0
    wrel
    @0
    c0
    wceq
    @5
    c0
    wceq
    wb
    cG
    releupth
    @0
    reldm0
    ax-mp
    necon3bii
    vf
    @5
    n0
    bitri
    @6
    @8
    vf
    @6
    @4
    vp
    cv
    #
    @0
    wbr
    #
    vp
    wex
    @8
    vp
    @4
    @0
    vf
    vex
    eldm
    @10
    @8
    vp
    @2
    @10
    @3
    vx
    @9
    @4
    cG
    cV
    eulerpathpr.v
    eulerpathpr
    expcom
    exlimiv
    sylbi
    exlimiv
    sylbi
    impcom
end
