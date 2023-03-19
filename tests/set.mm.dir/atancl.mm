include "catan.mm"
include "cfv.mm"
include "cc.mm"
include "wcel.mm"
include "ci.mm"
include "cneg.mm"
include "cpr.mm"
include "cdif.mm"
include "cdm.mm"
include "atanf.mm"
include "ffvelrni.mm"
include "fdmi.mm"
include "eleq2s.mm"

theorem atancl
  let cA: class A


  assert |- ( A e. dom arctan -> ( arctan ` A ) e. CC )

  proof
    cA
    catan
    cfv
    cc
    wcel
    cA
    cc
    ci
    cneg
    ci
    cpr
    cdif
    #
    catan
    cdm
    @0
    cc
    cA
    catan
    atanf
    ffvelrni
    @0
    cc
    catan
    atanf
    fdmi
    eleq2s
end
