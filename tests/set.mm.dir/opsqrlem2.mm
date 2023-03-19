include "c1.mm"
include "cfv.mm"
include "cn.mm"
include "ch0o.mm"
include "csn.mm"
include "cxp.mm"
include "cseq.mm"
include "fveq1i.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "1z.mm"
include "seq1.mm"
include "ax-mp.mm"
include "1nn.mm"
include "cho.mm"
include "0hmop.mm"
include "elexi.mm"
include "fvconst2.mm"
include "3eqtri.mm"

theorem opsqrlem2
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cT: class T
  let cF: class F
  let vj: setvar j
  let vk: setvar k
  let vw: setvar w
  let vz: setvar z
  let cG: class G
  let cN: class N
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
  assert |- ( F ` 1 ) = 0hop

  proof
    c1
    cF
    cfv
    c1
    cS
    cn
    ch0o
    csn
    cxp
    #
    c1
    cseq
    #
    cfv
    #
    c1
    @0
    cfv
    #
    ch0o
    c1
    cF
    @1
    opsqrlem2.3
    fveq1i
    c1
    cz
    wcel
    @2
    @3
    wceq
    1z
    cS
    @0
    c1
    seq1
    ax-mp
    c1
    cn
    wcel
    @3
    ch0o
    wceq
    1nn
    cn
    ch0o
    c1
    ch0o
    cho
    0hmop
    elexi
    fvconst2
    ax-mp
    3eqtri
end
