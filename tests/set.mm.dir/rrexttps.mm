include "crrext.mm"
include "wcel.mm"
include "cxme.mm"
include "ctps.mm"
include "cnrg.mm"
include "cngp.mm"
include "rrextnrg.mm"
include "nrgngp.mm"
include "ngpxms.mm"
include "3syl.mm"
include "xmstps.mm"
include "syl.mm"

theorem rrexttps
  let cR: class R


  assert |- ( R e. RRExt -> R e. TopSp )

  proof
    cR
    crrext
    wcel
    #
    cR
    cxme
    wcel
    #
    cR
    ctps
    wcel
    @0
    cR
    cnrg
    wcel
    cR
    cngp
    wcel
    @1
    cR
    rrextnrg
    cR
    nrgngp
    cR
    ngpxms
    3syl
    cR
    xmstps
    syl
end
