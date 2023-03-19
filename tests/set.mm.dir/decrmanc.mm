include "cc0.mm"
include "0nn0.mm"
include "dec0h.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "nn0mulcli.mm"
include "nn0cni.mm"
include "addid1i.mm"
include "eqtri.mm"
include "decma.mm"

theorem decrmanc
  let cA: class A
  let cB: class B
  let cP: class P
  let cE: class E
  let cF: class F
  let cM: class M
  let cN: class N
  assume decrmanc.a: |- A e. NN0
  assume decrmanc.b: |- B e. NN0
  assume decrmanc.n: |- N e. NN0
  assume decrmanc.m: |- M = ; A B
  assume decrmanc.p: |- P e. NN0
  assume decrmanc.e: |- ( A x. P ) = E
  assume decrmanc.f: |- ( ( B x. P ) + N ) = F


  assert |- ( ( M x. P ) + N ) = ; E F

  proof
    cA
    cB
    cc0
    cN
    cP
    cE
    cF
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
    cA
    cP
    cmul
    co
    #
    cc0
    caddc
    co
    @0
    cE
    @0
    @0
    cA
    cP
    decrmanc.a
    decrmanc.p
    nn0mulcli
    nn0cni
    addid1i
    decrmanc.e
    eqtri
    decrmanc.f
    decma
end
