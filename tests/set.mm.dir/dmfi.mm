include "cfn.mm"
include "wcel.mm"
include "cdm.mm"
include "cdom.mm"
include "wbr.mm"
include "fidomdm.mm"
include "domfi.mm"
include "mpdan.mm"

theorem dmfi
  let cA: class A


  assert |- ( A e. Fin -> dom A e. Fin )

  proof
    cA
    cfn
    wcel
    cA
    cdm
    #
    cA
    cdom
    wbr
    @0
    cfn
    wcel
    cA
    fidomdm
    cA
    @0
    domfi
    mpdan
end
