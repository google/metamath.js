include "cuspgr.mm"
include "wcel.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wf1.mm"
include "cedg.mm"
include "wf1o.mm"
include "eqid.mm"
include "uspgrf.mm"
include "crn.mm"
include "f1f1orn.mm"
include "wceq.mm"
include "wb.mm"
include "ciedg.mm"
include "rneqi.mm"
include "edgval.mm"
include "eqtr4i.mm"
include "f1oeq3.mm"
include "ax-mp.mm"
include "sylib.mm"
include "syl.mm"

theorem uspgrf1oedg
  let cE: class E
  let cG: class G
  let vx: setvar x
  assume usgrf1o.e: |- E = ( iEdg ` G )


  assert |- ( G e. USPGraph -> E : dom E -1-1-onto-> ( Edg ` G ) )

  proof
    cG
    cuspgr
    wcel
    cE
    cdm
    #
    vx
    cv
    chash
    cfv
    c2
    cle
    wbr
    vx
    cG
    cvtx
    cfv
    #
    cpw
    c0
    csn
    cdif
    crab
    #
    cE
    wf1
    #
    @0
    cG
    cedg
    cfv
    #
    cE
    wf1o
    #
    vx
    cE
    cG
    @1
    @1
    eqid
    usgrf1o.e
    uspgrf
    @3
    @0
    cE
    crn
    #
    cE
    wf1o
    #
    @5
    @0
    @2
    cE
    f1f1orn
    @6
    @4
    wceq
    @7
    @5
    wb
    @6
    cG
    ciedg
    cfv
    #
    crn
    @4
    cE
    @8
    usgrf1o.e
    rneqi
    cG
    edgval
    eqtr4i
    @6
    @4
    @0
    cE
    f1oeq3
    ax-mp
    sylib
    syl
end
