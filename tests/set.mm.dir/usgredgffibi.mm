include "cusgr.mm"
include "wcel.mm"
include "cfn.mm"
include "crn.mm"
include "cvv.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cvtx.mm"
include "cpw.mm"
include "crab.mm"
include "wf1.mm"
include "wb.mm"
include "ciedg.mm"
include "fvexi.mm"
include "eqid.mm"
include "usgrfs.mm"
include "f1vrnfibi.mm"
include "sylancr.mm"
include "cedg.mm"
include "edgval.mm"
include "eqcomi.mm"
include "rneqi.mm"
include "3eqtri.mm"
include "eleq1i.mm"
include "syl6rbbr.mm"

theorem usgredgffibi
  let cE: class E
  let cG: class G
  let cI: class I
  let vx: setvar x
  assume usgredgffibi.I: |- I = ( iEdg ` G )
  assume usgredgffibi.e: |- E = ( Edg ` G )


  assert |- ( G e. USGraph -> ( E e. Fin <-> I e. Fin ) )

  proof
    cG
    cusgr
    wcel
    #
    cI
    cfn
    wcel
    #
    cI
    crn
    #
    cfn
    wcel
    #
    cE
    cfn
    wcel
    @0
    cI
    cvv
    wcel
    cI
    cdm
    #
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
    crab
    #
    cI
    wf1
    @1
    @3
    wb
    cI
    cG
    ciedg
    usgredgffibi.I
    fvexi
    vx
    cI
    cG
    @5
    @5
    eqid
    usgredgffibi.I
    usgrfs
    @4
    @6
    cI
    cvv
    f1vrnfibi
    sylancr
    cE
    @2
    cfn
    cE
    cG
    cedg
    cfv
    cG
    ciedg
    cfv
    #
    crn
    @2
    usgredgffibi.e
    cG
    edgval
    @7
    cI
    cI
    @7
    usgredgffibi.I
    eqcomi
    rneqi
    3eqtri
    eleq1i
    syl6rbbr
end
