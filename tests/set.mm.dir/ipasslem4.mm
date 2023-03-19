include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "cc.mm"
include "nnrecre.mm"
include "recnd.mm"
include "cnv.mm"
include "phnvi.mm"
include "nvscl.mm"
include "mp3an1.mm"
include "sylan.mm"
include "dipcl.mm"
include "mp3an13.mm"
include "syl.mm"
include "mulcl.mm"
include "syl2an.mm"
include "nncn.mm"
include "adantr.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "recidd.mm"
include "oveq1d.mm"
include "mulid2d.mm"
include "sylan9eq.mm"
include "wceq.mm"
include "nvsid.mm"
include "mpan.mm"
include "simpr.mm"
include "w3a.mm"
include "nvsass.mm"
include "syl3anc.mm"
include "eqtr3d.mm"
include "cn0.mm"
include "nnnn0.mm"
include "ipasslem1.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "adantl.mm"
include "mulassd.mm"
include "mulcanad.mm"

theorem ipasslem4
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


  assert |- ( ( N e. NN /\ A e. X ) -> ( ( ( 1 / N ) S A ) P B ) = ( ( 1 / N ) x. ( A P B ) ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    c1
    cN
    cdiv
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
    @3
    cA
    cB
    cP
    co
    #
    cmul
    co
    #
    cN
    @2
    @4
    cX
    wcel
    #
    @5
    cc
    wcel
    #
    @0
    @3
    cc
    wcel
    #
    @1
    @8
    @0
    @3
    cN
    nnrecre
    recnd
    #
    cU
    cnv
    wcel
    #
    @10
    @1
    @8
    cU
    ip1i.9
    phnvi
    #
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
    #
    @12
    @8
    cB
    cX
    wcel
    #
    @9
    @13
    ipasslem1.b
    @4
    cB
    cP
    cU
    cX
    ip1i.1
    ip1i.7
    dipcl
    mp3an13
    syl
    @0
    @10
    @6
    cc
    wcel
    #
    @7
    cc
    wcel
    @1
    @11
    @12
    @1
    @15
    @16
    @13
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
    @6
    mulcl
    syl2an
    @0
    cN
    cc
    wcel
    #
    @1
    cN
    nncn
    #
    adantr
    #
    @0
    cN
    cc0
    wne
    @1
    cN
    nnne0
    #
    adantr
    @2
    cN
    @3
    cmul
    co
    #
    @6
    cmul
    co
    #
    cN
    @5
    cmul
    co
    #
    cN
    @7
    cmul
    co
    @2
    @23
    @6
    cN
    @4
    cS
    co
    #
    cB
    cP
    co
    #
    @24
    @0
    @1
    @23
    c1
    @6
    cmul
    co
    @6
    @0
    @22
    c1
    @6
    cmul
    @0
    cN
    @19
    @21
    recidd
    #
    oveq1d
    @1
    @6
    @17
    mulid2d
    sylan9eq
    @2
    cA
    @25
    cB
    cP
    @2
    @22
    cA
    cS
    co
    #
    cA
    @25
    @0
    @1
    @28
    c1
    cA
    cS
    co
    #
    cA
    @0
    @22
    c1
    cA
    cS
    @27
    oveq1d
    @12
    @1
    @29
    cA
    wceq
    @13
    cA
    cS
    cU
    cX
    ip1i.1
    ip1i.4
    nvsid
    mpan
    sylan9eq
    @2
    @18
    @10
    @1
    @28
    @25
    wceq
    #
    @20
    @0
    @10
    @1
    @11
    adantr
    #
    @0
    @1
    simpr
    @12
    @18
    @10
    @1
    w3a
    @30
    @13
    cN
    @3
    cA
    cS
    cU
    cX
    ip1i.1
    ip1i.4
    nvsass
    mpan
    syl3anc
    eqtr3d
    oveq1d
    @2
    cN
    cn0
    wcel
    #
    @8
    @26
    @24
    wceq
    @0
    @32
    @1
    cN
    nnnn0
    adantr
    @14
    @4
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
    syl2anc
    3eqtrd
    @2
    cN
    @3
    @6
    @20
    @31
    @1
    @16
    @0
    @17
    adantl
    mulassd
    eqtr3d
    mulcanad
end
