include "cumgr.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "w3a.mm"
include "cuhgr.mm"
include "ciedg.mm"
include "cdm.mm"
include "c2.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cpw.mm"
include "crab.mm"
include "wf.mm"
include "cvtxdg.mm"
include "cc0.mm"
include "umgruhgr.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "cupgr.mm"
include "eqid.mm"
include "umgrislfupgr.mm"
include "simprbi.mm"
include "3jca.mm"
include "simp2.mm"
include "vtxdlfuhgr1v.mm"
include "sylc.mm"

theorem vdumgr0
  let cG: class G
  let cN: class N
  let cV: class V
  let vx: setvar x
  assume vdumgr0.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. UMGraph /\ N e. V /\ ( # ` V ) = 1 ) -> ( ( VtxDeg ` G ) ` N ) = 0 )

  proof
    cG
    cumgr
    wcel
    #
    cN
    cV
    wcel
    #
    cV
    chash
    cfv
    c1
    wceq
    #
    w3a
    #
    cG
    cuhgr
    wcel
    #
    @2
    cG
    ciedg
    cfv
    #
    cdm
    c2
    vx
    cv
    chash
    cfv
    cle
    wbr
    vx
    cV
    cpw
    crab
    #
    @5
    wf
    #
    w3a
    @1
    cN
    cG
    cvtxdg
    cfv
    cfv
    cc0
    wceq
    @3
    @4
    @2
    @7
    @0
    @1
    @4
    @2
    cG
    umgruhgr
    3ad2ant1
    @0
    @1
    @2
    simp3
    @0
    @1
    @7
    @2
    @0
    cG
    cupgr
    wcel
    @7
    vx
    cG
    @5
    cV
    vdumgr0.v
    @5
    eqid
    #
    umgrislfupgr
    simprbi
    3ad2ant1
    3jca
    @0
    @1
    @2
    simp2
    vx
    cN
    @6
    cG
    @5
    cV
    vdumgr0.v
    @8
    @6
    eqid
    vtxdlfuhgr1v
    sylc
end
