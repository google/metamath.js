include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cmul.mm"
include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wceq.mm"
include "nn0cni.mm"
include "expp1.mm"
include "mp2an.mm"
include "oveq2i.mm"
include "3eqtr3i.mm"

theorem numexpp1
  let cA: class A
  let cC: class C
  let cM: class M
  let cN: class N
  assume numexp.1: |- A e. NN0
  assume numexpp1.2: |- M e. NN0
  assume numexpp1.3: |- ( M + 1 ) = N
  assume numexpp1.4: |- ( ( A ^ M ) x. A ) = C


  assert |- ( A ^ N ) = C

  proof
    cA
    cM
    c1
    caddc
    co
    #
    cexp
    co
    #
    cA
    cM
    cexp
    co
    cA
    cmul
    co
    #
    cA
    cN
    cexp
    co
    cC
    cA
    cc
    wcel
    cM
    cn0
    wcel
    @1
    @2
    wceq
    cA
    numexp.1
    nn0cni
    numexpp1.2
    cA
    cM
    expp1
    mp2an
    @0
    cN
    cA
    cexp
    numexpp1.3
    oveq2i
    numexpp1.4
    3eqtr3i
end
