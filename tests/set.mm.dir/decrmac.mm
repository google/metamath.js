include "cc0.mm"
include "0nn0.mm"
include "dec0h.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "nn0cni.mm"
include "addid2i.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "decmac.mm"

theorem decrmac
  let cA: class A
  let cB: class B
  let cP: class P
  let cE: class E
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  assume decrmanc.a: |- A e. NN0
  assume decrmanc.b: |- B e. NN0
  assume decrmanc.n: |- N e. NN0
  assume decrmanc.m: |- M = ; A B
  assume decrmanc.p: |- P e. NN0
  assume decrmac.f: |- F e. NN0
  assume decrmac.g: |- G e. NN0
  assume decrmac.e: |- ( ( A x. P ) + G ) = E
  assume decrmac.2: |- ( ( B x. P ) + N ) = ; G F


  assert |- ( ( M x. P ) + N ) = ; E F

  proof
    cA
    cB
    cc0
    cN
    cP
    cE
    cF
    cG
    cM
    cN
    decrmanc.a
    decrmanc.b
    0nn0
    decrmanc.n
    decrmanc.m
    cN
    decrmanc.n
    dec0h
    decrmanc.p
    decrmac.f
    decrmac.g
    cA
    cP
    cmul
    co
    #
    cc0
    cG
    caddc
    co
    #
    caddc
    co
    @0
    cG
    caddc
    co
    cE
    @1
    cG
    @0
    caddc
    cG
    cG
    decrmac.g
    nn0cni
    addid2i
    oveq2i
    decrmac.e
    eqtri
    decrmac.2
    decmac
end
