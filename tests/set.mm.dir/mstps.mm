include "cmt.mm"
include "wcel.mm"
include "cxme.mm"
include "ctps.mm"
include "msxms.mm"
include "xmstps.mm"
include "syl.mm"

theorem mstps
  let cM: class M


  assert |- ( M e. MetSp -> M e. TopSp )

  proof
    cM
    cmt
    wcel
    cM
    cxme
    wcel
    cM
    ctps
    wcel
    cM
    msxms
    cM
    xmstps
    syl
end
