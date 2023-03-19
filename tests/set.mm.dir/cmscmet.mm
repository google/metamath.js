include "ccms.mm"
include "wcel.mm"
include "cmt.mm"
include "cms.mm"
include "cfv.mm"
include "iscms.mm"
include "simprbi.mm"

theorem cmscmet
  let cD: class D
  let cM: class M
  let cX: class X
  let vb: setvar b
  let vw: setvar w
  assume iscms.1: |- X = ( Base ` M )
  assume iscms.2: |- D = ( ( dist ` M ) |` ( X X. X ) )


  assert |- ( M e. CMetSp -> D e. ( CMet ` X ) )

  proof
    cM
    ccms
    wcel
    cM
    cmt
    wcel
    cD
    cX
    cms
    cfv
    wcel
    cD
    cM
    cX
    iscms.1
    iscms.2
    iscms
    simprbi
end
