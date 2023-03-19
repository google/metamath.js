include "cxrs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cress.mm"
include "cmpt.mm"
include "ctsu.mm"
include "cuni.mm"
include "cesum.mm"
include "cbvmptf.mm"
include "oveq2i.mm"
include "unieqi.mm"
include "df-esum.mm"
include "3eqtr4i.mm"

theorem cbvesum
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  assume cbvesum.1: |- ( j = k -> B = C )
  assume cbvesum.2: |- F/_ k A
  assume cbvesum.3: |- F/_ j A
  assume cbvesum.4: |- F/_ k B
  assume cbvesum.5: |- F/_ j C

  disjoint j k
  assert |- sum* j e. A B = sum* k e. A C

  proof
    cxrs
    cc0
    cpnf
    cicc
    co
    cress
    co
    #
    vj
    cA
    cB
    cmpt
    #
    ctsu
    co
    #
    cuni
    @0
    vk
    cA
    cC
    cmpt
    #
    ctsu
    co
    #
    cuni
    cA
    cB
    vj
    cesum
    cA
    cC
    vk
    cesum
    @2
    @4
    @1
    @3
    @0
    ctsu
    vj
    vk
    cA
    cB
    cC
    cbvesum.3
    cbvesum.2
    cbvesum.4
    cbvesum.5
    cbvesum.1
    cbvmptf
    oveq2i
    unieqi
    cA
    cB
    vj
    df-esum
    cA
    cC
    vk
    df-esum
    3eqtr4i
end
