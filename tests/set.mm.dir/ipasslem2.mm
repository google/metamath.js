include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "co.mm"
include "cmul.mm"
include "cc.mm"
include "nn0cn.mm"
include "negcld.mm"
include "cnv.mm"
include "phnvi.mm"
include "dipcl.mm"
include "mp3an13.mm"
include "mulcl.mm"
include "syl2an.mm"
include "nvscl.mm"
include "mp3an1.mm"
include "sylan.mm"
include "syl.mm"
include "cmin.mm"
include "c1.mm"
include "caddc.mm"
include "cc0.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "mulneg2.mm"
include "mpan2.mm"
include "mulid1.mm"
include "negeqd.mm"
include "eqtr2d.mm"
include "adantr.mm"
include "oveq1d.mm"
include "neg1cn.mm"
include "w3a.mm"
include "nvsass.mm"
include "mpan.mm"
include "mp3an2.mm"
include "eqtrd.mm"
include "mp3an12.mm"
include "ipasslem1.mm"
include "sylan2.mm"
include "oveq2d.mm"
include "negsubd.mm"
include "mulneg1.mm"
include "adantl.mm"
include "adddid.mm"
include "ipdiri.mm"
include "mp3an3.mm"
include "mpdan.mm"
include "cn0v.mm"
include "cfv.mm"
include "eqid.mm"
include "nvrinv.mm"
include "dip0l.mm"
include "mp2an.mm"
include "syl6eq.mm"
include "eqtr3d.mm"
include "mul01d.mm"
include "sylan9eqr.mm"
include "3eqtr2d.mm"
include "subeq0d.mm"
include "eqcomd.mm"

theorem ipasslem2
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  let vj: setvar j
  let vk: setvar k
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  assume ip1i.1: |- X = ( BaseSet ` U )
  assume ip1i.2: |- G = ( +v ` U )
  assume ip1i.4: |- S = ( .sOLD ` U )
  assume ip1i.7: |- P = ( .iOLD ` U )
  assume ip1i.9: |- U e. CPreHilOLD
  assume ipasslem1.b: |- B e. X


  assert |- ( ( N e. NN0 /\ A e. X ) -> ( ( -u N S A ) P B ) = ( -u N x. ( A P B ) ) )

  proof
    cN
    cn0
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cN
    cneg
    #
    cA
    cB
    cP
    co
    #
    cmul
    co
    #
    @3
    cA
    cS
    co
    #
    cB
    cP
    co
    #
    @2
    @5
    @7
    @0
    @3
    cc
    wcel
    #
    @4
    cc
    wcel
    #
    @5
    cc
    wcel
    @1
    @0
    cN
    cN
    nn0cn
    #
    negcld
    #
    cU
    cnv
    wcel
    #
    @1
    cB
    cX
    wcel
    #
    @9
    cU
    ip1i.9
    phnvi
    #
    ipasslem1.b
    cA
    cB
    cP
    cU
    cX
    ip1i.1
    ip1i.7
    dipcl
    mp3an13
    #
    @3
    @4
    mulcl
    syl2an
    #
    @2
    @6
    cX
    wcel
    #
    @7
    cc
    wcel
    #
    @0
    @8
    @1
    @17
    @11
    @12
    @8
    @1
    @17
    @14
    @3
    cA
    cS
    cU
    cX
    ip1i.1
    ip1i.4
    nvscl
    mp3an1
    sylan
    @12
    @17
    @13
    @18
    @14
    ipasslem1.b
    @6
    cB
    cP
    cU
    cX
    ip1i.1
    ip1i.7
    dipcl
    mp3an13
    syl
    @2
    @5
    @7
    cmin
    co
    @5
    cN
    c1
    cneg
    #
    cA
    cS
    co
    #
    cB
    cP
    co
    #
    cmul
    co
    #
    cmin
    co
    @5
    @22
    cneg
    #
    caddc
    co
    #
    cc0
    @2
    @7
    @22
    @5
    cmin
    @2
    @7
    cN
    @20
    cS
    co
    #
    cB
    cP
    co
    #
    @22
    @2
    @6
    @25
    cB
    cP
    @0
    cN
    cc
    wcel
    #
    @1
    @6
    @25
    wceq
    @10
    @27
    @1
    wa
    #
    @6
    cN
    @19
    cmul
    co
    #
    cA
    cS
    co
    #
    @25
    @28
    @3
    @29
    cA
    cS
    @27
    @3
    @29
    wceq
    @1
    @27
    @29
    cN
    c1
    cmul
    co
    #
    cneg
    #
    @3
    @27
    c1
    cc
    wcel
    @29
    @32
    wceq
    ax-1cn
    cN
    c1
    mulneg2
    mpan2
    @27
    @31
    cN
    cN
    mulid1
    negeqd
    eqtr2d
    adantr
    oveq1d
    @27
    @19
    cc
    wcel
    #
    @1
    @30
    @25
    wceq
    #
    neg1cn
    @12
    @27
    @33
    @1
    w3a
    @34
    @14
    cN
    @19
    cA
    cS
    cU
    cX
    ip1i.1
    ip1i.4
    nvsass
    mpan
    mp3an2
    eqtrd
    sylan
    oveq1d
    @1
    @0
    @20
    cX
    wcel
    #
    @26
    @22
    wceq
    @12
    @33
    @1
    @35
    @14
    neg1cn
    @19
    cA
    cS
    cU
    cX
    ip1i.1
    ip1i.4
    nvscl
    mp3an12
    #
    @20
    cB
    cP
    cS
    cU
    cG
    cN
    cX
    ip1i.1
    ip1i.2
    ip1i.4
    ip1i.7
    ip1i.9
    ipasslem1.b
    ipasslem1
    sylan2
    eqtrd
    oveq2d
    @2
    @5
    @22
    @16
    @0
    @27
    @21
    cc
    wcel
    #
    @22
    cc
    wcel
    @1
    @10
    @1
    @35
    @37
    @36
    @12
    @35
    @13
    @37
    @14
    ipasslem1.b
    @20
    cB
    cP
    cU
    cX
    ip1i.1
    ip1i.7
    dipcl
    mp3an13
    syl
    #
    cN
    @21
    mulcl
    syl2an
    negsubd
    @2
    @5
    @3
    @21
    cmul
    co
    #
    caddc
    co
    #
    @24
    cc0
    @2
    @39
    @23
    @5
    caddc
    @0
    @27
    @37
    @39
    @23
    wceq
    @1
    @10
    @38
    cN
    @21
    mulneg1
    syl2an
    oveq2d
    @2
    @3
    @4
    @21
    caddc
    co
    #
    cmul
    co
    #
    @40
    cc0
    @2
    @3
    @4
    @21
    @0
    @8
    @1
    @11
    adantr
    @1
    @9
    @0
    @15
    adantl
    @1
    @37
    @0
    @38
    adantl
    adddid
    @1
    @0
    @42
    @3
    cc0
    cmul
    co
    cc0
    @1
    @41
    cc0
    @3
    cmul
    @1
    cA
    @20
    cG
    co
    #
    cB
    cP
    co
    #
    @41
    cc0
    @1
    @35
    @44
    @41
    wceq
    #
    @36
    @1
    @35
    @13
    @45
    ipasslem1.b
    cA
    @20
    cB
    cP
    cS
    cU
    cG
    cX
    ip1i.1
    ip1i.2
    ip1i.4
    ip1i.7
    ip1i.9
    ipdiri
    mp3an3
    mpdan
    @1
    @44
    cU
    cn0v
    cfv
    #
    cB
    cP
    co
    #
    cc0
    @1
    @43
    @46
    cB
    cP
    @12
    @1
    @43
    @46
    wceq
    @14
    cA
    cS
    cU
    cG
    cX
    @46
    ip1i.1
    ip1i.2
    ip1i.4
    @46
    eqid
    #
    nvrinv
    mpan
    oveq1d
    @12
    @13
    @47
    cc0
    wceq
    @14
    ipasslem1.b
    cB
    cP
    cU
    cX
    @46
    ip1i.1
    @48
    ip1i.7
    dip0l
    mp2an
    syl6eq
    eqtr3d
    oveq2d
    @0
    @3
    @11
    mul01d
    sylan9eqr
    eqtr3d
    eqtr3d
    3eqtr2d
    subeq0d
    eqcomd
end
