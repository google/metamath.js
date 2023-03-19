include "cfusgr.mm"
include "wcel.mm"
include "crusgr.mm"
include "wbr.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cn0.mm"
include "3simpb.mm"
include "cusgr.mm"
include "cxnn0.mm"
include "eqid.mm"
include "rusgrprop0.mm"
include "simp3d.mm"
include "3ad2ant2.mm"
include "fusgrregdegfi.mm"
include "sylc.mm"

theorem frusgrnn0
  let cG: class G
  let cK: class K
  let cV: class V
  let vv: setvar v
  assume frusgrnn0.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. FinUSGraph /\ G RegUSGraph K /\ V =/= (/) ) -> K e. NN0 )

  proof
    cG
    cfusgr
    wcel
    #
    cG
    cK
    crusgr
    wbr
    #
    cV
    c0
    wne
    #
    w3a
    @0
    @2
    wa
    vv
    cv
    cG
    cvtxdg
    cfv
    #
    cfv
    cK
    wceq
    vv
    cV
    wral
    #
    cK
    cn0
    wcel
    @0
    @1
    @2
    3simpb
    @1
    @0
    @4
    @2
    @1
    cG
    cusgr
    wcel
    cK
    cxnn0
    wcel
    @4
    vv
    @3
    cG
    cK
    cV
    frusgrnn0.v
    @3
    eqid
    #
    rusgrprop0
    simp3d
    3ad2ant2
    vv
    @3
    cG
    cK
    cV
    frusgrnn0.v
    @5
    fusgrregdegfi
    sylc
end
