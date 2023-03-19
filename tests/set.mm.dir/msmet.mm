include "cmt.mm"
include "wcel.mm"
include "cme.mm"
include "cfv.mm"
include "ctopn.mm"
include "cmopn.mm"
include "wceq.mm"
include "eqid.mm"
include "isms2.mm"
include "simplbi.mm"

theorem msmet
  let cD: class D
  let cM: class M
  let cX: class X
  assume msf.x: |- X = ( Base ` M )
  assume msf.d: |- D = ( ( dist ` M ) |` ( X X. X ) )


  assert |- ( M e. MetSp -> D e. ( Met ` X ) )

  proof
    cM
    cmt
    wcel
    cD
    cX
    cme
    cfv
    wcel
    cM
    ctopn
    cfv
    #
    cD
    cmopn
    cfv
    wceq
    cD
    @0
    cM
    cX
    @0
    eqid
    msf.x
    msf.d
    isms2
    simplbi
end
