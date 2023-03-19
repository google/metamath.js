include "chash.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cpw.mm"
include "crab.mm"
include "cbc.mm"
include "fveq2i.mm"
include "cfn.mm"
include "wcel.mm"
include "cz.mm"
include "fzfi.mm"
include "nnzi.mm"
include "hashbc.mm"
include "mp2an.mm"
include "cn0.mm"
include "cn.mm"
include "wa.mm"
include "pm3.2i.mm"
include "nnaddcl.mm"
include "nnnn0.mm"
include "mp2b.mm"
include "hashfz1.mm"
include "ax-mp.mm"
include "oveq1i.mm"
include "3eqtr2i.mm"

theorem ballotlem1
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
  assert |- ( # ` O ) = ( ( M + N ) _C M )

  proof
    cO
    chash
    cfv
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
    crab
    #
    chash
    cfv
    #
    @1
    chash
    cfv
    #
    cM
    cbc
    co
    #
    @0
    cM
    cbc
    co
    cO
    @2
    chash
    ballotth.o
    fveq2i
    @1
    cfn
    wcel
    cM
    cz
    wcel
    @5
    @3
    wceq
    c1
    @0
    fzfi
    cM
    ballotth.m
    nnzi
    vc
    @1
    cM
    hashbc
    mp2an
    @4
    @0
    cM
    cbc
    @0
    cn0
    wcel
    #
    @4
    @0
    wceq
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    @0
    cn
    wcel
    @6
    @7
    @8
    ballotth.m
    ballotth.n
    pm3.2i
    cM
    cN
    nnaddcl
    @0
    nnnn0
    mp2b
    @0
    hashfz1
    ax-mp
    oveq1i
    3eqtr2i
end
