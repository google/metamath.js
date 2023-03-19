include "cq.mm"
include "wcel.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "cv.mm"
include "cdiv.mm"
include "cn.mm"
include "wrex.mm"
include "cz.mm"
include "wi.mm"
include "elq.mm"
include "wa.mm"
include "w3a.mm"
include "c1.mm"
include "cc.mm"
include "zcn.mm"
include "nnrecre.mm"
include "recnd.mm"
include "cnv.mm"
include "phnvi.mm"
include "dipcl.mm"
include "mp3an13.mm"
include "mulass.mm"
include "syl3an.mm"
include "adantr.mm"
include "nncn.mm"
include "adantl.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "divrecd.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "id.mm"
include "nvsass.mm"
include "mpan.mm"
include "eqtrd.mm"
include "nvscl.mm"
include "mp3an1.mm"
include "sylan.mm"
include "ipasslem3.mm"
include "sylan2.mm"
include "3impb.mm"
include "ipasslem4.mm"
include "3adant1.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "3eqtr4rd.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "3expia.mm"
include "com23.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "imp.mm"

theorem ipasslem5
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cU: class U
  let cG: class G
  let cX: class X
  let vj: setvar j
  let vk: setvar k
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  assume ip1i.1: |- X = ( BaseSet ` U )
  assume ip1i.2: |- G = ( +v ` U )
  assume ip1i.4: |- S = ( .sOLD ` U )
  assume ip1i.7: |- P = ( .iOLD ` U )
  assume ip1i.9: |- U e. CPreHilOLD
  assume ipasslem1.b: |- B e. X


  assert |- ( ( C e. QQ /\ A e. X ) -> ( ( C S A ) P B ) = ( C x. ( A P B ) ) )

  proof
    cC
    cq
    wcel
    #
    cA
    cX
    wcel
    #
    cC
    cA
    cS
    co
    #
    cB
    cP
    co
    #
    cC
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
    cC
    vj
    cv
    #
    vk
    cv
    #
    cdiv
    co
    #
    wceq
    #
    vk
    cn
    wrex
    vj
    cz
    wrex
    @1
    @6
    wi
    #
    vj
    vk
    cC
    elq
    @10
    @11
    vj
    vk
    cz
    cn
    @7
    cz
    wcel
    #
    @8
    cn
    wcel
    #
    wa
    #
    @1
    @10
    @6
    @12
    @13
    @1
    @10
    @6
    wi
    @12
    @13
    @1
    w3a
    #
    @6
    @10
    @9
    cA
    cS
    co
    #
    cB
    cP
    co
    #
    @9
    @4
    cmul
    co
    #
    wceq
    @15
    @7
    c1
    @8
    cdiv
    co
    #
    cmul
    co
    #
    @4
    cmul
    co
    #
    @7
    @19
    @4
    cmul
    co
    #
    cmul
    co
    #
    @18
    @17
    @12
    @7
    cc
    wcel
    #
    @13
    @19
    cc
    wcel
    #
    @1
    @4
    cc
    wcel
    #
    @21
    @23
    wceq
    @7
    zcn
    #
    @13
    @19
    @8
    nnrecre
    recnd
    #
    cU
    cnv
    wcel
    #
    @1
    cB
    cX
    wcel
    @26
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
    @7
    @19
    @4
    mulass
    syl3an
    @15
    @9
    @20
    @4
    cmul
    @12
    @13
    @9
    @20
    wceq
    @1
    @14
    @7
    @8
    @12
    @24
    @13
    @27
    adantr
    @13
    @8
    cc
    wcel
    @12
    @8
    nncn
    adantl
    @13
    @8
    cc0
    wne
    @12
    @8
    nnne0
    adantl
    divrecd
    3adant3
    #
    oveq1d
    @15
    @17
    @7
    @19
    cA
    cS
    co
    #
    cS
    co
    #
    cB
    cP
    co
    #
    @7
    @32
    cB
    cP
    co
    #
    cmul
    co
    #
    @23
    @15
    @16
    @33
    cB
    cP
    @15
    @16
    @20
    cA
    cS
    co
    #
    @33
    @15
    @9
    @20
    cA
    cS
    @31
    oveq1d
    @12
    @24
    @13
    @25
    @1
    @1
    @37
    @33
    wceq
    #
    @27
    @28
    @1
    id
    @29
    @24
    @25
    @1
    w3a
    @38
    @30
    @7
    @19
    cA
    cS
    cU
    cX
    ip1i.1
    ip1i.4
    nvsass
    mpan
    syl3an
    eqtrd
    oveq1d
    @12
    @13
    @1
    @34
    @36
    wceq
    #
    @13
    @1
    wa
    @12
    @32
    cX
    wcel
    #
    @39
    @13
    @25
    @1
    @40
    @28
    @29
    @25
    @1
    @40
    @30
    @19
    cA
    cS
    cU
    cX
    ip1i.1
    ip1i.4
    nvscl
    mp3an1
    sylan
    @32
    cB
    cP
    cS
    cU
    cG
    @7
    cX
    ip1i.1
    ip1i.2
    ip1i.4
    ip1i.7
    ip1i.9
    ipasslem1.b
    ipasslem3
    sylan2
    3impb
    @15
    @35
    @22
    @7
    cmul
    @13
    @1
    @35
    @22
    wceq
    @12
    cA
    cB
    cP
    cS
    cU
    cG
    @8
    cX
    ip1i.1
    ip1i.2
    ip1i.4
    ip1i.7
    ip1i.9
    ipasslem1.b
    ipasslem4
    3adant1
    oveq2d
    3eqtrd
    3eqtr4rd
    @10
    @3
    @17
    @5
    @18
    @10
    @2
    @16
    cB
    cP
    cC
    @9
    cA
    cS
    oveq1
    oveq1d
    cC
    @9
    @4
    cmul
    oveq1
    eqeq12d
    syl5ibrcom
    3expia
    com23
    rexlimivv
    sylbi
    imp
end
