include "cusgr.mm"
include "wcel.mm"
include "cdm.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wf1.mm"
include "wf.mm"
include "eqid.mm"
include "usgrf.mm"
include "f1f.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "simprbi.mm"

theorem usgredg2ALT
  let cE: class E
  let cG: class G
  let cX: class X
  let vx: setvar x
  assume usgredg2.e: |- E = ( iEdg ` G )


  assert |- ( ( G e. USGraph /\ X e. dom E ) -> ( # ` ( E ` X ) ) = 2 )

  proof
    cG
    cusgr
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
    cG
    cvtx
    cfv
    #
    cpw
    c0
    csn
    cdif
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
    @8
    cX
    cE
    @0
    @1
    @8
    cE
    wf1
    @1
    @8
    cE
    wf
    vx
    cE
    cG
    @6
    @6
    eqid
    usgredg2.e
    usgrf
    @1
    @8
    cE
    f1f
    syl
    ffvelrnda
    @9
    @2
    @7
    wcel
    @11
    @5
    @11
    vx
    @2
    @7
    @3
    @2
    wceq
    @4
    @10
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
