include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "ccoe.mm"
include "fveq2.mm"
include "3eqtr4g.mm"
include "w3a.mm"
include "cc.mm"
include "cc0.mm"
include "cdgr.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "ccnv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cn0.mm"
include "clt.mm"
include "csup.mm"
include "simp3.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "supeq1d.mm"
include "dgrval.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "3eqtr4d.mm"
include "oveq2d.mm"
include "simpl3.mm"
include "fveq1d.mm"
include "oveq1d.mm"
include "sumeq12dv.mm"
include "mpteq2dv.mm"
include "eqid.mm"
include "coeid.mm"
include "3expia.mm"
include "impbid2.mm"

theorem coe11
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let cG: class G
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  let cN: class N
  assume coefv0.1: |- A = ( coeff ` F )
  assume coeadd.2: |- B = ( coeff ` G )


  assert |- ( ( F e. ( Poly ` S ) /\ G e. ( Poly ` S ) ) -> ( F = G <-> A = B ) )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    cG
    @0
    wcel
    #
    wa
    cF
    cG
    wceq
    #
    cA
    cB
    wceq
    #
    @3
    cF
    ccoe
    cfv
    cG
    ccoe
    cfv
    cA
    cB
    cF
    cG
    ccoe
    fveq2
    coefv0.1
    coeadd.2
    3eqtr4g
    @1
    @2
    @4
    @3
    @1
    @2
    @4
    w3a
    #
    vz
    cc
    cc0
    cF
    cdgr
    cfv
    #
    cfz
    co
    #
    vk
    cv
    #
    cA
    cfv
    #
    vz
    cv
    @8
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    #
    vz
    cc
    cc0
    cG
    cdgr
    cfv
    #
    cfz
    co
    #
    @8
    cB
    cfv
    #
    @10
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    #
    cF
    cG
    @5
    vz
    cc
    @12
    @18
    @5
    @7
    @15
    @11
    @17
    vk
    @5
    @6
    @14
    cc0
    cfz
    @5
    cA
    ccnv
    #
    cc
    cc0
    csn
    cdif
    #
    cima
    #
    cn0
    clt
    csup
    #
    cB
    ccnv
    #
    @21
    cima
    #
    cn0
    clt
    csup
    #
    @6
    @14
    @5
    cn0
    @22
    @25
    clt
    @5
    @20
    @24
    @21
    @5
    cA
    cB
    @1
    @2
    @4
    simp3
    cnveqd
    imaeq1d
    supeq1d
    @1
    @2
    @6
    @23
    wceq
    @4
    cA
    cS
    cF
    coefv0.1
    dgrval
    3ad2ant1
    @2
    @1
    @14
    @26
    wceq
    @4
    cB
    cS
    cG
    coeadd.2
    dgrval
    3ad2ant2
    3eqtr4d
    oveq2d
    @5
    @8
    @7
    wcel
    #
    wa
    #
    @9
    @16
    @10
    cmul
    @28
    @8
    cA
    cB
    @1
    @2
    @4
    @27
    simpl3
    fveq1d
    oveq1d
    sumeq12dv
    mpteq2dv
    @1
    @2
    cF
    @13
    wceq
    @4
    vz
    cA
    cS
    vk
    cF
    @6
    coefv0.1
    @6
    eqid
    coeid
    3ad2ant1
    @2
    @1
    cG
    @19
    wceq
    @4
    vz
    cB
    cS
    vk
    cG
    @14
    coeadd.2
    @14
    eqid
    coeid
    3ad2ant2
    3eqtr4d
    3expia
    impbid2
end
