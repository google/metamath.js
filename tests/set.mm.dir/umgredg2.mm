include "cumgr.mm"
include "wcel.mm"
include "cdm.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "umgrf.mm"
include "ffvelrnda.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "simprbi.mm"
include "syl.mm"

theorem umgredg2
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let ve: setvar e
  let vg: setvar g
  let vh: setvar h
  let vv: setvar v
  let vx: setvar x
  assume isumgr.v: |- V = ( Vtx ` G )
  assume isumgr.e: |- E = ( iEdg ` G )


  assert |- ( ( G e. UMGraph /\ X e. dom E ) -> ( # ` ( E ` X ) ) = 2 )

  proof
    cG
    cumgr
    wcel
    #
    cX
    cE
    cdm
    #
    wcel
    wa
    cX
    cE
    cfv
    #
    vx
    cv
    #
    chash
    cfv
    #
    c2
    wceq
    #
    vx
    cV
    cpw
    #
    crab
    #
    wcel
    #
    @2
    chash
    cfv
    #
    c2
    wceq
    #
    @0
    @1
    @7
    cX
    cE
    vx
    cE
    cG
    cV
    isumgr.v
    isumgr.e
    umgrf
    ffvelrnda
    @8
    @2
    @6
    wcel
    @10
    @5
    @10
    vx
    @2
    @6
    @3
    @2
    wceq
    @4
    @9
    c2
    @3
    @2
    chash
    fveq2
    eqeq1d
    elrab
    simprbi
    syl
end
