include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "c2.mm"
include "nn0cni.mm"
include "2timesi.mm"
include "eqtr3i.mm"
include "oveq2i.mm"
include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wceq.mm"
include "expadd.mm"
include "mp3an.mm"
include "eqtri.mm"
include "oveq12i.mm"

theorem numexp2x
  let cA: class A
  let cC: class C
  let cD: class D
  let cM: class M
  let cN: class N
  assume numexp.1: |- A e. NN0
  assume numexpp1.2: |- M e. NN0
  assume numexp2x.3: |- ( 2 x. M ) = N
  assume numexp2x.4: |- ( A ^ M ) = D
  assume numexp2x.5: |- ( D x. D ) = C


  assert |- ( A ^ N ) = C

  proof
    cA
    cN
    cexp
    co
    #
    cA
    cM
    cexp
    co
    #
    @1
    cmul
    co
    #
    cC
    @0
    cA
    cM
    cM
    caddc
    co
    #
    cexp
    co
    #
    @2
    cN
    @3
    cA
    cexp
    c2
    cM
    cmul
    co
    cN
    @3
    numexp2x.3
    cM
    cM
    numexpp1.2
    nn0cni
    2timesi
    eqtr3i
    oveq2i
    cA
    cc
    wcel
    cM
    cn0
    wcel
    #
    @5
    @4
    @2
    wceq
    cA
    numexp.1
    nn0cni
    numexpp1.2
    numexpp1.2
    cA
    cM
    cM
    expadd
    mp3an
    eqtri
    @2
    cD
    cD
    cmul
    co
    cC
    @1
    cD
    @1
    cD
    cmul
    numexp2x.4
    numexp2x.4
    oveq12i
    numexp2x.5
    eqtri
    eqtri
end
