include "cccinfty.mm"
include "cc.mm"
include "cun.mm"
include "cccbar.mm"
include "ssun2.mm"
include "df-bj-ccbar.mm"
include "sseqtr4i.mm"

theorem bj-ccinftyssccbar



  assert |- CCinfty C_ CCbar

  proof
    cccinfty
    cc
    cccinfty
    cun
    cccbar
    cccinfty
    cc
    ssun2
    df-bj-ccbar
    sseqtr4i
end
