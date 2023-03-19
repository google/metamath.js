include "cc0.mm"
include "0nn0.mm"
include "decaddc.mm"

theorem decaddc2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cM: class M
  let cN: class N
  assume decma.a: |- A e. NN0
  assume decma.b: |- B e. NN0
  assume decma.c: |- C e. NN0
  assume decma.d: |- D e. NN0
  assume decma.m: |- M = ; A B
  assume decma.n: |- N = ; C D
  assume decaddc.e: |- ( ( A + C ) + 1 ) = E
  assume decaddc2.t: |- ( B + D ) = ; 1 0


  assert |- ( M + N ) = ; E 0

  proof
    cA
    cB
    cC
    cD
    cE
    cc0
    cM
    cN
    decma.a
    decma.b
    decma.c
    decma.d
    decma.m
    decma.n
    decaddc.e
    0nn0
    decaddc2.t
    decaddc
end
