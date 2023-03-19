include "cmt.mm"
include "wcel.mm"
include "cme.mm"
include "cfv.mm"
include "cxp.mm"
include "cr.mm"
include "wf.mm"
include "msmet.mm"
include "metf.mm"
include "syl.mm"

theorem msf
  let cD: class D
  let cM: class M
  let cX: class X
  assume msf.x: |- X = ( Base ` M )
  assume msf.d: |- D = ( ( dist ` M ) |` ( X X. X ) )


  assert |- ( M e. MetSp -> D : ( X X. X ) --> RR )

  proof
    cM
    cmt
    wcel
    cD
    cX
    cme
    cfv
    wcel
    cX
    cX
    cxp
    cr
    cD
    wf
    cD
    cM
    cX
    msf.x
    msf.d
    msmet
    cD
    cX
    metf
    syl
end
