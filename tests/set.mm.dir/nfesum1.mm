include "cesum.mm"
include "cxrs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cress.mm"
include "cmpt.mm"
include "ctsu.mm"
include "cuni.mm"
include "df-esum.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfov.mm"
include "nfuni.mm"
include "nfcxfr.mm"

theorem nfesum1
  let cA: class A
  let cB: class B
  let vk: setvar k
  assume nfesum1.1: |- F/_ k A


  assert |- F/_ k sum* k e. A B

  proof
    vk
    cA
    cB
    vk
    cesum
    cxrs
    cc0
    cpnf
    cicc
    co
    cress
    co
    #
    vk
    cA
    cB
    cmpt
    #
    ctsu
    co
    #
    cuni
    cA
    cB
    vk
    df-esum
    vk
    @2
    vk
    @0
    @1
    ctsu
    vk
    @0
    nfcv
    vk
    ctsu
    nfcv
    vk
    cA
    cB
    nfmpt1
    nfov
    nfuni
    nfcxfr
end
