include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfv.mm"
include "ch0o.mm"
include "csn.mm"
include "cxp.mm"
include "c2.mm"
include "cdiv.mm"
include "ccom.mm"
include "chod.mm"
include "chot.mm"
include "chos.mm"
include "cseq.mm"
include "cuz.mm"
include "wceq.mm"
include "elnnuz.mm"
include "seqp1.mm"
include "sylbi.mm"
include "fveq1i.mm"
include "oveq1i.mm"
include "3eqtr4g.mm"
include "cho.mm"
include "opsqrlem4.mm"
include "ffvelrni.mm"
include "peano2nn.mm"
include "0hmop.mm"
include "elexi.mm"
include "fvconst2.mm"
include "syl.mm"
include "syl6eqel.mm"
include "opsqrlem3.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem opsqrlem5
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cT: class T
  let cF: class F
  let cN: class N
  let vj: setvar j
  let vk: setvar k
  let vw: setvar w
  let vz: setvar z
  let cG: class G
  let cH: class H
  assume opsqrlem2.1: |- T e. HrmOp
  assume opsqrlem2.2: |- S = ( x e. HrmOp , y e. HrmOp |-> ( x +op ( ( 1 / 2 ) .op ( T -op ( x o. x ) ) ) ) )
  assume opsqrlem2.3: |- F = seq 1 ( S , ( NN X. { 0hop } ) )

  disjoint x y
  disjoint T x
  disjoint T y
  disjoint j k
  disjoint F j
  disjoint F k
  disjoint w z
  disjoint G w
  disjoint G z
  disjoint N j
  disjoint N k
  disjoint S w
  disjoint S z
  disjoint w x
  disjoint w y
  disjoint T w
  disjoint x z
  disjoint y z
  disjoint T z
  disjoint H w
  disjoint H z
  assert |- ( N e. NN -> ( F ` ( N + 1 ) ) = ( ( F ` N ) +op ( ( 1 / 2 ) .op ( T -op ( ( F ` N ) o. ( F ` N ) ) ) ) ) )

  proof
    cN
    cn
    wcel
    #
    cN
    c1
    caddc
    co
    #
    cF
    cfv
    #
    cN
    cF
    cfv
    #
    @1
    cn
    ch0o
    csn
    cxp
    #
    cfv
    #
    cS
    co
    #
    @3
    c1
    c2
    cdiv
    co
    cT
    @3
    @3
    ccom
    chod
    co
    chot
    co
    chos
    co
    #
    @0
    @1
    cS
    @4
    c1
    cseq
    #
    cfv
    #
    cN
    @8
    cfv
    #
    @5
    cS
    co
    #
    @2
    @6
    @0
    cN
    c1
    cuz
    cfv
    wcel
    @9
    @11
    wceq
    cN
    elnnuz
    cS
    @4
    c1
    cN
    seqp1
    sylbi
    @1
    cF
    @8
    opsqrlem2.3
    fveq1i
    @3
    @10
    @5
    cS
    cN
    cF
    @8
    opsqrlem2.3
    fveq1i
    oveq1i
    3eqtr4g
    @0
    @3
    cho
    wcel
    @5
    cho
    wcel
    @6
    @7
    wceq
    cn
    cho
    cN
    cF
    vx
    vy
    cS
    cT
    cF
    opsqrlem2.1
    opsqrlem2.2
    opsqrlem2.3
    opsqrlem4
    ffvelrni
    @0
    @5
    ch0o
    cho
    @0
    @1
    cn
    wcel
    @5
    ch0o
    wceq
    cN
    peano2nn
    cn
    ch0o
    @1
    ch0o
    cho
    0hmop
    elexi
    fvconst2
    syl
    0hmop
    syl6eqel
    vx
    vy
    cS
    cT
    cF
    @3
    @5
    opsqrlem2.1
    opsqrlem2.2
    opsqrlem2.3
    opsqrlem3
    syl2anc
    eqtrd
end
