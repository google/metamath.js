include "ccphlo.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "cns.mm"
include "cfv.mm"
include "co.mm"
include "cpv.mm"
include "caddc.mm"
include "cmin.mm"
include "wceq.mm"
include "idd.mm"
include "cnv.mm"
include "phnv.mm"
include "cc.mm"
include "neg1cn.mm"
include "eqid.mm"
include "nvscl.mm"
include "mp3an2.mm"
include "sylan.mm"
include "ex.mm"
include "3anim123d.mm"
include "imp.mm"
include "dipdir.mm"
include "syldan.mm"
include "nvmval.mm"
include "syl3an1.mm"
include "3adant3r3.mm"
include "oveq1d.mm"
include "cmul.mm"
include "dipass.mm"
include "mp3anr1.mm"
include "dipcl.mm"
include "3expb.mm"
include "mulm1d.mm"
include "eqtrd.mm"
include "3adantr1.mm"
include "oveq2d.mm"
include "3adant3r2.mm"
include "3adant3r1.mm"
include "negsubd.mm"
include "eqtr2d.mm"
include "3eqtr4d.mm"

theorem dipsubdir
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cU: class U
  let cM: class M
  let cX: class X
  assume ipsubdir.1: |- X = ( BaseSet ` U )
  assume ipsubdir.3: |- M = ( -v ` U )
  assume ipsubdir.7: |- P = ( .iOLD ` U )


  assert |- ( ( U e. CPreHilOLD /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A M B ) P C ) = ( ( A P C ) - ( B P C ) ) )

  proof
    cU
    ccphlo
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cC
    cX
    wcel
    #
    w3a
    #
    wa
    #
    cA
    c1
    cneg
    #
    cB
    cU
    cns
    cfv
    #
    co
    #
    cU
    cpv
    cfv
    #
    co
    #
    cC
    cP
    co
    #
    cA
    cC
    cP
    co
    #
    @8
    cC
    cP
    co
    #
    caddc
    co
    #
    cA
    cB
    cM
    co
    #
    cC
    cP
    co
    @12
    cB
    cC
    cP
    co
    #
    cmin
    co
    #
    @0
    @4
    @1
    @8
    cX
    wcel
    #
    @3
    w3a
    #
    @11
    @14
    wceq
    @0
    @4
    @19
    @0
    @1
    @1
    @2
    @18
    @3
    @3
    @0
    @1
    idd
    @0
    @2
    @18
    @0
    cU
    cnv
    wcel
    #
    @2
    @18
    cU
    phnv
    #
    @20
    @6
    cc
    wcel
    #
    @2
    @18
    neg1cn
    @6
    cB
    @7
    cU
    cX
    ipsubdir.1
    @7
    eqid
    #
    nvscl
    mp3an2
    sylan
    ex
    @0
    @3
    idd
    3anim123d
    imp
    cA
    @8
    cC
    cP
    cU
    @9
    cX
    ipsubdir.1
    @9
    eqid
    #
    ipsubdir.7
    dipdir
    syldan
    @5
    @15
    @10
    cC
    cP
    @0
    @1
    @2
    @15
    @10
    wceq
    #
    @3
    @0
    @20
    @1
    @2
    @25
    @21
    cA
    cB
    @7
    cU
    @9
    cM
    cX
    ipsubdir.1
    @24
    @23
    ipsubdir.3
    nvmval
    syl3an1
    3adant3r3
    oveq1d
    @5
    @14
    @12
    @16
    cneg
    #
    caddc
    co
    #
    @17
    @5
    @13
    @26
    @12
    caddc
    @0
    @2
    @3
    @13
    @26
    wceq
    @1
    @0
    @2
    @3
    wa
    #
    wa
    #
    @13
    @6
    @16
    cmul
    co
    #
    @26
    @0
    @22
    @2
    @3
    @13
    @30
    wceq
    neg1cn
    @6
    cB
    cC
    cP
    @7
    cU
    cX
    ipsubdir.1
    @23
    ipsubdir.7
    dipass
    mp3anr1
    @29
    @16
    @0
    @20
    @28
    @16
    cc
    wcel
    #
    @21
    @20
    @2
    @3
    @31
    cB
    cC
    cP
    cU
    cX
    ipsubdir.1
    ipsubdir.7
    dipcl
    #
    3expb
    sylan
    mulm1d
    eqtrd
    3adantr1
    oveq2d
    @0
    @20
    @4
    @27
    @17
    wceq
    @21
    @20
    @4
    wa
    @12
    @16
    @20
    @1
    @3
    @12
    cc
    wcel
    @2
    cA
    cC
    cP
    cU
    cX
    ipsubdir.1
    ipsubdir.7
    dipcl
    3adant3r2
    @20
    @2
    @3
    @31
    @1
    @32
    3adant3r1
    negsubd
    sylan
    eqtr2d
    3eqtr4d
end
