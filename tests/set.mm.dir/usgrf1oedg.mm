include "cusgr.mm"
include "wcel.mm"
include "cdm.mm"
include "wf1o.mm"
include "crn.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wf1.mm"
include "eqid.mm"
include "usgrf.mm"
include "f1f1orn.mm"
include "syl.mm"
include "cedg.mm"
include "ciedg.mm"
include "edgval.mm"
include "a1i.mm"
include "eqcomi.mm"
include "rneqi.mm"
include "syl6eq.mm"
include "syl5eq.mm"
include "f1oeq3d.mm"
include "mpbird.mm"

theorem usgrf1oedg
  let cE: class E
  let cG: class G
  let cI: class I
  let vx: setvar x
  assume usgrf1oedg.i: |- I = ( iEdg ` G )
  assume usgrf1oedg.e: |- E = ( Edg ` G )


  assert |- ( G e. USGraph -> I : dom I -1-1-onto-> E )

  proof
    cG
    cusgr
    wcel
    #
    cI
    cdm
    #
    cE
    cI
    wf1o
    @1
    cI
    crn
    #
    cI
    wf1o
    #
    @0
    @1
    vx
    cv
    chash
    cfv
    c2
    wceq
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
    cI
    wf1
    @3
    vx
    cI
    cG
    @4
    @4
    eqid
    usgrf1oedg.i
    usgrf
    @1
    @5
    cI
    f1f1orn
    syl
    @0
    cE
    @2
    @1
    cI
    @0
    cE
    cG
    cedg
    cfv
    #
    @2
    usgrf1oedg.e
    @0
    @6
    cG
    ciedg
    cfv
    #
    crn
    #
    @2
    @6
    @8
    wceq
    @0
    cG
    edgval
    a1i
    @7
    cI
    cI
    @7
    usgrf1oedg.i
    eqcomi
    rneqi
    syl6eq
    syl5eq
    f1oeq3d
    mpbird
end
