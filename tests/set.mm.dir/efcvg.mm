include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "cc0.mm"
include "cseq.mm"
include "cn0.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "cdiv.mm"
include "csu.mm"
include "ce.mm"
include "cli.mm"
include "nn0uz.mm"
include "0zd.mm"
include "wceq.mm"
include "eftval.mm"
include "adantl.mm"
include "eftcl.mm"
include "efcllem.mm"
include "isumclim2.mm"
include "efval.mm"
include "breqtrrd.mm"

theorem efcvg
  let cA: class A
  let vn: setvar n
  let cF: class F
  let vk: setvar k
  assume efcvg.1: |- F = ( n e. NN0 |-> ( ( A ^ n ) / ( ! ` n ) ) )

  disjoint A n
  disjoint k n
  disjoint A k
  disjoint F k
  assert |- ( A e. CC -> seq 0 ( + , F ) ~~> ( exp ` A ) )

  proof
    cA
    cc
    wcel
    #
    caddc
    cF
    cc0
    cseq
    cn0
    cA
    vk
    cv
    #
    cexp
    co
    @1
    cfa
    cfv
    cdiv
    co
    #
    vk
    csu
    cA
    ce
    cfv
    cli
    @0
    @2
    vk
    cF
    cc0
    cn0
    nn0uz
    @0
    0zd
    @1
    cn0
    wcel
    @1
    cF
    cfv
    @2
    wceq
    @0
    cA
    vn
    cF
    @1
    efcvg.1
    eftval
    adantl
    cA
    @1
    eftcl
    cA
    vn
    cF
    efcvg.1
    efcllem
    isumclim2
    cA
    vk
    efval
    breqtrrd
end
