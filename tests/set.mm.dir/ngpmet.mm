include "cngp.mm"
include "wcel.mm"
include "cmt.mm"
include "cme.mm"
include "cfv.mm"
include "ngpms.mm"
include "msmet.mm"
include "syl.mm"

theorem ngpmet
  let cD: class D
  let cG: class G
  let cX: class X
  assume ngpmet.x: |- X = ( Base ` G )
  assume ngpmet.d: |- D = ( ( dist ` G ) |` ( X X. X ) )


  assert |- ( G e. NrmGrp -> D e. ( Met ` X ) )

  proof
    cG
    cngp
    wcel
    cG
    cmt
    wcel
    cD
    cX
    cme
    cfv
    wcel
    cG
    ngpms
    cD
    cG
    cX
    ngpmet.x
    ngpmet.d
    msmet
    syl
end
