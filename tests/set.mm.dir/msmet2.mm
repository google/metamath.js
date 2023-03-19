include "cxp.mm"
include "cres.mm"
include "cds.mm"
include "cfv.mm"
include "reseq1i.mm"
include "msmet.mm"

theorem msmet2
  let cD: class D
  let cM: class M
  let cX: class X
  assume mscl.x: |- X = ( Base ` M )
  assume mscl.d: |- D = ( dist ` M )


  assert |- ( M e. MetSp -> ( D |` ( X X. X ) ) e. ( Met ` X ) )

  proof
    cD
    cX
    cX
    cxp
    #
    cres
    cM
    cX
    mscl.x
    cD
    cM
    cds
    cfv
    @0
    mscl.d
    reseq1i
    msmet
end
