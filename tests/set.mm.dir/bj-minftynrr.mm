include "cminfty.mm"
include "cc.mm"
include "wcel.mm"
include "cpi.mm"
include "cinftyexpi.mm"
include "cfv.mm"
include "bj-inftyexpidisj.mm"
include "df-bj-minfty.mm"
include "eleq1i.mm"
include "mtbir.mm"

theorem bj-minftynrr



  assert |- -. minfty e. CC

  proof
    cminfty
    cc
    wcel
    cpi
    cinftyexpi
    cfv
    #
    cc
    wcel
    cpi
    bj-inftyexpidisj
    cminfty
    @0
    cc
    df-bj-minfty
    eleq1i
    mtbir
end
