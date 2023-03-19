include "cc.mm"
include "wcel.mm"
include "cn.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "ccxp.mm"
include "csu.mm"
include "cmul.mm"
include "csgm.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "eqid.mm"
include "ssrab2.mm"
include "simpr.mm"
include "sseldi.mm"
include "nncnd.mm"
include "simpll.mm"
include "cxpcld.mm"
include "adantrr.mm"
include "nnred.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "adantrl.mm"
include "mulcxpd.mm"
include "eqcomd.mm"
include "oveq1.mm"
include "fsumdvdsmul.mm"
include "sgmval.mm"
include "syldan.mm"
include "oveq12d.mm"
include "nnmulcld.mm"
include "3eqtr4rd.mm"

theorem sgmmul
  let cA: class A
  let cM: class M
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let cP: class P
  let cK: class K


  assert |- ( ( A e. CC /\ ( M e. NN /\ N e. NN /\ ( M gcd N ) = 1 ) ) -> ( A sigma ( M x. N ) ) = ( ( A sigma M ) x. ( A sigma N ) ) )

  proof
    cA
    cc
    wcel
    #
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    cM
    cN
    cgcd
    co
    c1
    wceq
    #
    w3a
    #
    wa
    #
    vx
    cv
    #
    cM
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    vj
    cv
    #
    cA
    ccxp
    co
    #
    vj
    csu
    #
    @6
    cN
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    vk
    cv
    #
    cA
    ccxp
    co
    #
    vk
    csu
    #
    cmul
    co
    @6
    cM
    cN
    cmul
    co
    #
    cdvds
    wbr
    vx
    cn
    crab
    #
    vi
    cv
    #
    cA
    ccxp
    co
    #
    vi
    csu
    #
    cA
    cM
    csgm
    co
    #
    cA
    cN
    csgm
    co
    #
    cmul
    co
    cA
    @17
    csgm
    co
    #
    @5
    vx
    @10
    @15
    @20
    @9
    @14
    cmul
    co
    #
    cA
    ccxp
    co
    #
    vi
    vj
    vk
    cM
    cN
    @8
    @13
    @18
    @0
    @1
    @2
    @3
    simpr1
    #
    @0
    @1
    @2
    @3
    simpr2
    #
    @0
    @1
    @2
    @3
    simpr3
    @8
    eqid
    @13
    eqid
    @18
    eqid
    @5
    @9
    @8
    wcel
    #
    wa
    #
    @9
    cA
    @30
    @9
    @30
    @8
    cn
    @9
    @7
    vx
    cn
    ssrab2
    @5
    @29
    simpr
    sseldi
    #
    nncnd
    @0
    @4
    @29
    simpll
    cxpcld
    @5
    @14
    @13
    wcel
    #
    wa
    #
    @14
    cA
    @33
    @14
    @33
    @13
    cn
    @14
    @12
    vx
    cn
    ssrab2
    @5
    @32
    simpr
    sseldi
    #
    nncnd
    @0
    @4
    @32
    simpll
    cxpcld
    @5
    @29
    @32
    wa
    #
    wa
    #
    @26
    @10
    @15
    cmul
    co
    @36
    @9
    @14
    cA
    @36
    @9
    @5
    @29
    @9
    cn
    wcel
    @32
    @31
    adantrr
    #
    nnred
    @36
    @9
    @36
    @9
    @37
    nnnn0d
    nn0ge0d
    @36
    @14
    @5
    @32
    @14
    cn
    wcel
    @29
    @34
    adantrl
    #
    nnred
    @36
    @14
    @36
    @14
    @38
    nnnn0d
    nn0ge0d
    @0
    @4
    @35
    simpll
    mulcxpd
    eqcomd
    @19
    @25
    cA
    ccxp
    oveq1
    fsumdvdsmul
    @5
    @22
    @11
    @23
    @16
    cmul
    @0
    @4
    @1
    @22
    @11
    wceq
    @27
    cA
    cM
    vj
    vx
    sgmval
    syldan
    @0
    @4
    @2
    @23
    @16
    wceq
    @28
    cA
    cN
    vk
    vx
    sgmval
    syldan
    oveq12d
    @0
    @4
    @17
    cn
    wcel
    @24
    @21
    wceq
    @5
    cM
    cN
    @27
    @28
    nnmulcld
    cA
    @17
    vi
    vx
    sgmval
    syldan
    3eqtr4rd
end
