include "cho.mm"
include "cv.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "ccom.mm"
include "chod.mm"
include "chot.mm"
include "chos.mm"
include "wceq.mm"
include "id.mm"
include "coeq12d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "eqidd.mm"
include "cmpt2.mm"
include "weq.mm"
include "cbvmpt2v.mm"
include "eqtri.mm"
include "ovex.mm"
include "ovmpt2.mm"

theorem opsqrlem3
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let vj: setvar j
  let vk: setvar k
  let vw: setvar w
  let vz: setvar z
  let cN: class N
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
  assert |- ( ( G e. HrmOp /\ H e. HrmOp ) -> ( G S H ) = ( G +op ( ( 1 / 2 ) .op ( T -op ( G o. G ) ) ) ) )

  proof
    vz
    vw
    cG
    cH
    cho
    cho
    vz
    cv
    #
    c1
    c2
    cdiv
    co
    #
    cT
    @0
    @0
    ccom
    #
    chod
    co
    #
    chot
    co
    #
    chos
    co
    #
    cG
    @1
    cT
    cG
    cG
    ccom
    #
    chod
    co
    #
    chot
    co
    #
    chos
    co
    #
    cS
    @9
    @0
    cG
    wceq
    #
    @0
    cG
    @4
    @8
    chos
    @10
    id
    #
    @10
    @3
    @7
    @1
    chot
    @10
    @2
    @6
    cT
    chod
    @10
    @0
    cG
    @0
    cG
    @11
    @11
    coeq12d
    oveq2d
    oveq2d
    oveq12d
    vw
    cv
    cH
    wceq
    @9
    eqidd
    cS
    vx
    vy
    cho
    cho
    vx
    cv
    #
    @1
    cT
    @12
    @12
    ccom
    #
    chod
    co
    #
    chot
    co
    #
    chos
    co
    #
    cmpt2
    vz
    vw
    cho
    cho
    @5
    cmpt2
    opsqrlem2.2
    vx
    vy
    vz
    vw
    cho
    cho
    @16
    @5
    @5
    vx
    vz
    weq
    #
    @12
    @0
    @15
    @4
    chos
    @17
    id
    #
    @17
    @14
    @3
    @1
    chot
    @17
    @13
    @2
    cT
    chod
    @17
    @12
    @0
    @12
    @0
    @18
    @18
    coeq12d
    oveq2d
    oveq2d
    oveq12d
    vy
    vw
    weq
    @5
    eqidd
    cbvmpt2v
    eqtri
    cG
    @8
    chos
    ovex
    ovmpt2
end
