include "cbn.mm"
include "wcel.mm"
include "ccms.mm"
include "cms.mm"
include "cfv.mm"
include "bncms.mm"
include "cmscmet.mm"
include "syl.mm"

theorem bncmet
  let cD: class D
  let cM: class M
  let cX: class X
  let vb: setvar b
  let vw: setvar w
  assume iscms.1: |- X = ( Base ` M )
  assume iscms.2: |- D = ( ( dist ` M ) |` ( X X. X ) )


  assert |- ( M e. Ban -> D e. ( CMet ` X ) )

  proof
    cM
    cbn
    wcel
    cM
    ccms
    wcel
    cD
    cX
    cms
    cfv
    wcel
    cM
    bncms
    cD
    cM
    cX
    iscms.1
    iscms.2
    cmscmet
    syl
end
