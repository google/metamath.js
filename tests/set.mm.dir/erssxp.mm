include "wer.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "wrel.mm"
include "wss.mm"
include "errel.mm"
include "relssdmrn.mm"
include "syl.mm"
include "erdm.mm"
include "errn.mm"
include "xpeq12d.mm"
include "sseqtrd.mm"

theorem erssxp
  let cA: class A
  let cR: class R


  assert |- ( R Er A -> R C_ ( A X. A ) )

  proof
    cA
    cR
    wer
    #
    cR
    cR
    cdm
    #
    cR
    crn
    #
    cxp
    #
    cA
    cA
    cxp
    @0
    cR
    wrel
    cR
    @3
    wss
    cA
    cR
    errel
    cR
    relssdmrn
    syl
    @0
    @1
    cA
    @2
    cA
    cA
    cR
    erdm
    cA
    cR
    errn
    xpeq12d
    sseqtrd
end
