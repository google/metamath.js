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
include "nfmpt.mm"
include "nfov.mm"
include "nfuni.mm"
include "nfcxfr.mm"

theorem nfesum2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  assume nfesum2.1: |- F/_ x A
  assume nfesum2.2: |- F/_ x B

  disjoint k x
  assert |- F/_ x sum* k e. A B

  proof
    vx
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
    vx
    @2
    vx
    @0
    @1
    ctsu
    vx
    @0
    nfcv
    vx
    ctsu
    nfcv
    vx
    vk
    cA
    cB
    nfesum2.1
    nfesum2.2
    nfmpt
    nfov
    nfuni
    nfcxfr
end
