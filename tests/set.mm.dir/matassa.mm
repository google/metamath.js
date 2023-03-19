include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cvsca.mm"
include "cotp.mm"
include "cmmul.mm"
include "co.mm"
include "cxp.mm"
include "cmap.mm"
include "eqid.mm"
include "matbas2.mm"
include "matsca2.mm"
include "eqidd.mm"
include "matmulr.mm"
include "crg.mm"
include "clmod.mm"
include "crngring.mm"
include "matlmod.mm"
include "sylan2.mm"
include "matring.mm"
include "simpr.mm"
include "cv.mm"
include "w3a.mm"
include "csn.mm"
include "cmulr.mm"
include "cof.mm"
include "ad2antlr.mm"
include "simpll.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "mamuvs1.mm"
include "wceq.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "matvsca2.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "mamucl.mm"
include "3eqtr4d.mm"
include "simplr.mm"
include "mamuvs2.mm"
include "oveq2d.mm"
include "isassad.mm"

theorem matassa
  let cA: class A
  let cR: class R
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume matassa.a: |- A = ( N Mat R )


  assert |- ( ( N e. Fin /\ R e. CRing ) -> A e. AssAlg )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    wa
    #
    vy
    vz
    cR
    cbs
    cfv
    #
    cA
    cvsca
    cfv
    #
    cR
    cN
    cN
    cN
    cotp
    cmmul
    co
    #
    cR
    @3
    cN
    cN
    cxp
    #
    cmap
    co
    #
    cA
    vx
    cA
    cR
    @3
    cN
    ccrg
    matassa.a
    @3
    eqid
    #
    matbas2
    #
    cA
    cR
    cN
    ccrg
    matassa.a
    matsca2
    @2
    @3
    eqidd
    @2
    @4
    eqidd
    cA
    cR
    @5
    cN
    ccrg
    matassa.a
    @5
    eqid
    #
    matmulr
    @1
    @0
    cR
    crg
    wcel
    #
    cA
    clmod
    wcel
    cR
    crngring
    #
    cA
    cR
    cN
    matassa.a
    matlmod
    sylan2
    @1
    @0
    @11
    cA
    crg
    wcel
    @12
    cA
    cR
    cN
    matassa.a
    matring
    sylan2
    @0
    @1
    simpr
    @2
    vx
    cv
    #
    @3
    wcel
    #
    vy
    cv
    #
    @7
    wcel
    #
    vz
    cv
    #
    @7
    wcel
    #
    w3a
    #
    wa
    #
    @6
    @13
    csn
    cxp
    #
    @15
    cR
    cmulr
    cfv
    #
    cof
    #
    co
    #
    @17
    @5
    co
    @21
    @15
    @17
    @5
    co
    #
    @23
    co
    #
    @13
    @15
    @4
    co
    #
    @17
    @5
    co
    @13
    @25
    @4
    co
    #
    @20
    @3
    cR
    @22
    @5
    cN
    cN
    cN
    @13
    @15
    @17
    @8
    @1
    @11
    @0
    @19
    @12
    ad2antlr
    #
    @10
    @0
    @1
    @19
    simpll
    #
    @30
    @30
    @22
    eqid
    #
    @2
    @14
    @16
    @18
    simpr1
    #
    @2
    @14
    @16
    @18
    simpr2
    #
    @2
    @14
    @16
    @18
    simpr3
    #
    mamuvs1
    @20
    @27
    @24
    @17
    @5
    @20
    @14
    @15
    cA
    cbs
    cfv
    #
    wcel
    @27
    @24
    wceq
    @32
    @20
    @15
    @7
    @35
    @33
    @2
    @7
    @35
    wceq
    @19
    @9
    adantr
    #
    eleqtrd
    cA
    @35
    @6
    cR
    @4
    @22
    @3
    cN
    @13
    @15
    matassa.a
    @35
    eqid
    #
    @8
    @4
    eqid
    #
    @31
    @6
    eqid
    #
    matvsca2
    syl2anc
    oveq1d
    @20
    @14
    @25
    @35
    wcel
    @28
    @26
    wceq
    @32
    @20
    @25
    @7
    @35
    @20
    @3
    cN
    cR
    @5
    cN
    cN
    @15
    @17
    @8
    @29
    @10
    @30
    @30
    @30
    @33
    @34
    mamucl
    @36
    eleqtrd
    cA
    @35
    @6
    cR
    @4
    @22
    @3
    cN
    @13
    @25
    matassa.a
    @37
    @8
    @38
    @31
    @39
    matvsca2
    syl2anc
    #
    3eqtr4d
    @20
    @15
    @21
    @17
    @23
    co
    #
    @5
    co
    @26
    @15
    @13
    @17
    @4
    co
    #
    @5
    co
    @28
    @20
    @3
    cR
    @22
    @5
    cN
    cN
    cN
    @15
    @13
    @17
    @0
    @1
    @19
    simplr
    @8
    @31
    @10
    @30
    @30
    @30
    @33
    @32
    @34
    mamuvs2
    @20
    @42
    @41
    @15
    @5
    @20
    @14
    @17
    @35
    wcel
    @42
    @41
    wceq
    @32
    @20
    @17
    @7
    @35
    @34
    @36
    eleqtrd
    cA
    @35
    @6
    cR
    @4
    @22
    @3
    cN
    @13
    @17
    matassa.a
    @37
    @8
    @38
    @31
    @39
    matvsca2
    syl2anc
    oveq2d
    @40
    3eqtr4d
    isassad
end
