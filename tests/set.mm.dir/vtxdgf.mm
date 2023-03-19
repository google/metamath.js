include "wcel.mm"
include "cxnn0.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "ciedg.mm"
include "cdm.mm"
include "crab.mm"
include "chash.mm"
include "csn.mm"
include "wceq.mm"
include "cxad.mm"
include "co.mm"
include "cmpt.mm"
include "wa.mm"
include "cvv.mm"
include "eqid.mm"
include "fvex.mm"
include "dmexg.mm"
include "mp1i.mm"
include "rabexd.mm"
include "hashxnn0.mm"
include "syl.mm"
include "xnn0xaddcl.mm"
include "syl2anc.mm"
include "fmptd.mm"
include "vtxdgfval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem vtxdgf
  let cG: class G
  let cV: class V
  let cW: class W
  let vu: setvar u
  let vx: setvar x
  assume vtxdgf.v: |- V = ( Vtx ` G )


  assert |- ( G e. W -> ( VtxDeg ` G ) : V --> NN0* )

  proof
    cG
    cW
    wcel
    #
    cV
    cxnn0
    cG
    cvtxdg
    cfv
    #
    wf
    cV
    cxnn0
    vu
    cV
    vu
    cv
    #
    vx
    cv
    cG
    ciedg
    cfv
    #
    cfv
    #
    wcel
    #
    vx
    @3
    cdm
    #
    crab
    #
    chash
    cfv
    #
    @4
    @2
    csn
    wceq
    #
    vx
    @6
    crab
    #
    chash
    cfv
    #
    cxad
    co
    #
    cmpt
    #
    wf
    @0
    vu
    cV
    @12
    cxnn0
    @13
    @0
    @2
    cV
    wcel
    wa
    #
    @8
    cxnn0
    wcel
    #
    @11
    cxnn0
    wcel
    #
    @12
    cxnn0
    wcel
    @14
    @7
    cvv
    wcel
    @15
    @14
    @5
    vx
    @6
    @7
    cvv
    @7
    eqid
    @3
    cvv
    wcel
    @6
    cvv
    wcel
    @14
    cG
    ciedg
    fvex
    @3
    cvv
    dmexg
    mp1i
    #
    rabexd
    @7
    cvv
    hashxnn0
    syl
    @14
    @10
    cvv
    wcel
    @16
    @14
    @9
    vx
    @6
    @10
    cvv
    @10
    eqid
    @17
    rabexd
    @10
    cvv
    hashxnn0
    syl
    @8
    @11
    xnn0xaddcl
    syl2anc
    @13
    eqid
    fmptd
    @0
    cV
    cxnn0
    @1
    @13
    vx
    vu
    @6
    cG
    @3
    cV
    cW
    vtxdgf.v
    @3
    eqid
    @6
    eqid
    vtxdgfval
    feq1d
    mpbird
end
