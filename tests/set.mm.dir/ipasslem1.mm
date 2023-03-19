include "cn0.mm"
include "wcel.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "wa.mm"
include "cc.mm"
include "nn0cn.mm"
include "ax-1cn.mm"
include "cnv.mm"
include "w3a.mm"
include "phnvi.mm"
include "nvdir.mm"
include "mpan.mm"
include "mp3an2.mm"
include "sylan.mm"
include "nvsid.mm"
include "adantl.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "dipcl.mm"
include "mp3an13.mm"
include "mulid2d.mm"
include "nvscl.mm"
include "mp3an1.mm"
include "ipdiri.mm"
include "mp3an3.mm"
include "sylancom.mm"
include "eqtr4d.mm"
include "oveq1.mm"
include "sylan9eq.mm"
include "adddir.mm"
include "syl2an.mm"
include "adantr.mm"
include "exp31.mm"
include "a2d.mm"
include "cn0v.mm"
include "cfv.mm"
include "eqid.mm"
include "dip0l.mm"
include "mp2an.mm"
include "nv0.mm"
include "mul02d.mm"
include "3eqtr4a.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "nn0indALT.mm"
include "imp.mm"

theorem ipasslem1
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


  assert |- ( ( N e. NN0 /\ A e. X ) -> ( ( N S A ) P B ) = ( N x. ( A P B ) ) )

  proof
    cN
    cn0
    wcel
    cA
    cX
    wcel
    #
    cN
    cA
    cS
    co
    #
    cB
    cP
    co
    #
    cN
    cA
    cB
    cP
    co
    #
    cmul
    co
    #
    wceq
    #
    @0
    vj
    cv
    #
    cA
    cS
    co
    #
    cB
    cP
    co
    #
    @6
    @3
    cmul
    co
    #
    wceq
    #
    wi
    @0
    cc0
    cA
    cS
    co
    #
    cB
    cP
    co
    #
    cc0
    @3
    cmul
    co
    #
    wceq
    #
    wi
    @0
    vk
    cv
    #
    cA
    cS
    co
    #
    cB
    cP
    co
    #
    @15
    @3
    cmul
    co
    #
    wceq
    #
    wi
    @0
    @15
    c1
    caddc
    co
    #
    cA
    cS
    co
    #
    cB
    cP
    co
    #
    @20
    @3
    cmul
    co
    #
    wceq
    #
    wi
    @0
    @5
    wi
    vj
    vk
    cN
    @15
    cn0
    wcel
    #
    @0
    @19
    @24
    @25
    @0
    @19
    @24
    @25
    @0
    wa
    #
    @19
    wa
    @22
    @18
    c1
    @3
    cmul
    co
    #
    caddc
    co
    #
    @23
    @26
    @19
    @22
    @17
    @27
    caddc
    co
    #
    @28
    @26
    @22
    @16
    cA
    cG
    co
    #
    cB
    cP
    co
    #
    @29
    @26
    @21
    @30
    cB
    cP
    @26
    @21
    @16
    c1
    cA
    cS
    co
    #
    cG
    co
    #
    @30
    @25
    @15
    cc
    wcel
    #
    @0
    @21
    @33
    wceq
    #
    @15
    nn0cn
    #
    @34
    c1
    cc
    wcel
    #
    @0
    @35
    ax-1cn
    cU
    cnv
    wcel
    #
    @34
    @37
    @0
    w3a
    @35
    cU
    ip1i.9
    phnvi
    #
    @15
    c1
    cA
    cS
    cU
    cG
    cX
    ip1i.1
    ip1i.2
    ip1i.4
    nvdir
    mpan
    mp3an2
    sylan
    @26
    @32
    cA
    @16
    cG
    @0
    @32
    cA
    wceq
    #
    @25
    @38
    @0
    @40
    @39
    cA
    cS
    cU
    cX
    ip1i.1
    ip1i.4
    nvsid
    mpan
    adantl
    oveq2d
    eqtrd
    oveq1d
    @26
    @29
    @17
    @3
    caddc
    co
    #
    @31
    @26
    @27
    @3
    @17
    caddc
    @0
    @27
    @3
    wceq
    @25
    @0
    @3
    @38
    @0
    cB
    cX
    wcel
    #
    @3
    cc
    wcel
    #
    @39
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
    mulid2d
    adantl
    oveq2d
    @25
    @0
    @16
    cX
    wcel
    #
    @31
    @41
    wceq
    #
    @25
    @34
    @0
    @45
    @36
    @38
    @34
    @0
    @45
    @39
    @15
    cA
    cS
    cU
    cX
    ip1i.1
    ip1i.4
    nvscl
    mp3an1
    sylan
    @45
    @0
    @42
    @46
    ipasslem1.b
    @16
    cA
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
    sylancom
    eqtr4d
    eqtr4d
    @17
    @18
    @27
    caddc
    oveq1
    sylan9eq
    @26
    @23
    @28
    wceq
    #
    @19
    @25
    @34
    @43
    @47
    @0
    @36
    @44
    @34
    @37
    @43
    @47
    ax-1cn
    @15
    c1
    @3
    adddir
    mp3an2
    syl2an
    adantr
    eqtr4d
    exp31
    a2d
    @0
    cU
    cn0v
    cfv
    #
    cB
    cP
    co
    #
    cc0
    @12
    @13
    @38
    @42
    @49
    cc0
    wceq
    @39
    ipasslem1.b
    cB
    cP
    cU
    cX
    @48
    ip1i.1
    @48
    eqid
    #
    ip1i.7
    dip0l
    mp2an
    @0
    @11
    @48
    cB
    cP
    @38
    @0
    @11
    @48
    wceq
    @39
    cA
    cS
    cU
    cX
    @48
    ip1i.1
    ip1i.4
    @50
    nv0
    mpan
    oveq1d
    @0
    @3
    @44
    mul02d
    3eqtr4a
    @6
    cc0
    wceq
    #
    @10
    @14
    @0
    @51
    @8
    @12
    @9
    @13
    @51
    @7
    @11
    cB
    cP
    @6
    cc0
    cA
    cS
    oveq1
    oveq1d
    @6
    cc0
    @3
    cmul
    oveq1
    eqeq12d
    imbi2d
    @6
    @15
    wceq
    #
    @10
    @19
    @0
    @52
    @8
    @17
    @9
    @18
    @52
    @7
    @16
    cB
    cP
    @6
    @15
    cA
    cS
    oveq1
    oveq1d
    @6
    @15
    @3
    cmul
    oveq1
    eqeq12d
    imbi2d
    @6
    @20
    wceq
    #
    @10
    @24
    @0
    @53
    @8
    @22
    @9
    @23
    @53
    @7
    @21
    cB
    cP
    @6
    @20
    cA
    cS
    oveq1
    oveq1d
    @6
    @20
    @3
    cmul
    oveq1
    eqeq12d
    imbi2d
    @6
    cN
    wceq
    #
    @10
    @5
    @0
    @54
    @8
    @2
    @9
    @4
    @54
    @7
    @1
    cB
    cP
    @6
    cN
    cA
    cS
    oveq1
    oveq1d
    @6
    cN
    @3
    cmul
    oveq1
    eqeq12d
    imbi2d
    nn0indALT
    imp
end
