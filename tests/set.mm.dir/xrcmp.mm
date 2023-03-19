include "cii.mm"
include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "chmph.mm"
include "wbr.mm"
include "ccmp.mm"
include "wcel.mm"
include "xrhmph.mm"
include "iicmp.mm"
include "cmphmph.mm"
include "mp2.mm"

theorem xrcmp



  assert |- ( ordTop ` <_ ) e. Comp

  proof
    cii
    cle
    cordt
    cfv
    #
    chmph
    wbr
    cii
    ccmp
    wcel
    @0
    ccmp
    wcel
    xrhmph
    iicmp
    cii
    @0
    cmphmph
    mp2
end
