include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cpw.mm"
include "ovex.mm"
include "pwex.mm"
include "rabex2.mm"

theorem ballotlemoex
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  assume ballotth.m: |- M e. NN
  assume ballotth.n: |- N e. NN
  assume ballotth.o: |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M }

  disjoint M c
  disjoint N c
  disjoint O c
  disjoint M i
  disjoint N i
  disjoint O i
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint M k
  disjoint N k
  disjoint O k
  assert |- O e. _V

  proof
    vc
    cv
    chash
    cfv
    cM
    wceq
    vc
    c1
    cM
    cN
    caddc
    co
    #
    cfz
    co
    #
    cpw
    cO
    ballotth.o
    @1
    c1
    @0
    cfz
    ovex
    pwex
    rabex2
end
