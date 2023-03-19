include "cpinfty.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cinftyexpi.mm"
include "cfv.mm"
include "bj-inftyexpidisj.mm"
include "df-bj-pinfty.mm"
include "eleq1i.mm"
include "mtbir.mm"

theorem bj-pinftynrr



  assert |- -. pinfty e. CC

  proof
    cpinfty
    cc
    wcel
    cc0
    cinftyexpi
    cfv
    #
    cc
    wcel
    cc0
    bj-inftyexpidisj
    cpinfty
    @0
    cc
    df-bj-pinfty
    eleq1i
    mtbir
end
