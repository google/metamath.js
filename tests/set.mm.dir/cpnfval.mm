include "cc.mm"
include "wss.mm"
include "cpw.mm"
include "wcel.mm"
include "ccpn.mm"
include "cfv.mm"
include "cn0.mm"
include "cv.mm"
include "cdvn.mm"
include "co.mm"
include "cdm.mm"
include "ccncf.mm"
include "cpm.mm"
include "crab.mm"
include "cmpt.mm"
include "wceq.mm"
include "cnex.mm"
include "elpw2.mm"
include "oveq2.mm"
include "oveq1.mm"
include "fveq1d.mm"
include "eleq1d.mm"
include "rabeqbidv.mm"
include "mpteq2dv.mm"
include "df-cpn.mm"
include "nn0ex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "sylbir.mm"

theorem cpnfval
  let cS: class S
  let vf: setvar f
  let vn: setvar n
  let vk: setvar k
  let vx: setvar x
  let cF: class F
  let vm: setvar m
  let cM: class M
  let cN: class N
  let vs: setvar s

  disjoint f n
  disjoint S f
  disjoint S n
  disjoint f k
  disjoint f x
  disjoint F f
  disjoint k n
  disjoint k x
  disjoint F k
  disjoint n x
  disjoint F n
  disjoint F x
  disjoint f m
  disjoint M f
  disjoint k m
  disjoint M k
  disjoint m n
  disjoint M m
  disjoint M n
  disjoint N f
  disjoint N n
  disjoint N x
  disjoint f s
  disjoint k s
  disjoint S k
  disjoint m s
  disjoint m x
  disjoint S m
  disjoint n s
  disjoint s x
  disjoint S s
  disjoint S x
  assert |- ( S C_ CC -> ( C^n ` S ) = ( n e. NN0 |-> { f e. ( CC ^pm S ) | ( ( S Dn f ) ` n ) e. ( dom f -cn-> CC ) } ) )

  proof
    cS
    cc
    wss
    cS
    cc
    cpw
    #
    wcel
    cS
    ccpn
    cfv
    vn
    cn0
    vn
    cv
    #
    cS
    vf
    cv
    #
    cdvn
    co
    #
    cfv
    #
    @2
    cdm
    cc
    ccncf
    co
    #
    wcel
    #
    vf
    cc
    cS
    cpm
    co
    #
    crab
    #
    cmpt
    #
    wceq
    cS
    cc
    cnex
    elpw2
    vs
    cS
    vn
    cn0
    @1
    vs
    cv
    #
    @2
    cdvn
    co
    #
    cfv
    #
    @5
    wcel
    #
    vf
    cc
    @10
    cpm
    co
    #
    crab
    #
    cmpt
    @9
    @0
    ccpn
    @10
    cS
    wceq
    #
    vn
    cn0
    @15
    @8
    @16
    @13
    @6
    vf
    @14
    @7
    @10
    cS
    cc
    cpm
    oveq2
    @16
    @12
    @4
    @5
    @16
    @1
    @11
    @3
    @10
    cS
    @2
    cdvn
    oveq1
    fveq1d
    eleq1d
    rabeqbidv
    mpteq2dv
    vn
    vf
    vs
    df-cpn
    vn
    cn0
    @8
    nn0ex
    mptex
    fvmpt
    sylbir
end
