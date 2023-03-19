include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "ccnp.mm"
include "co.mm"
include "wf.mm"
include "cflf.mm"
include "wa.mm"
include "cnpf2.mm"
include "3expa.mm"
include "3adantl3.mm"
include "cflim.mm"
include "simpl1.mm"
include "simpl3.mm"
include "csn.mm"
include "cnei.mm"
include "neiflim.mm"
include "oveq2i.mm"
include "syl6eleqr.mm"
include "syl2anc.mm"
include "simpr.mm"
include "cnpflfi.mm"
include "jca.mm"
include "cv.mm"
include "cima.mm"
include "wss.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cuni.mm"
include "ctop.mm"
include "wb.mm"
include "topontop.mm"
include "syl.mm"
include "wceq.mm"
include "toponuni.mm"
include "eleqtrd.mm"
include "eleq2i.mm"
include "eqid.mm"
include "isneip.mm"
include "syl5bb.mm"
include "sstr2.mm"
include "imass2.mm"
include "syl11.mm"
include "anim2d.mm"
include "reximdv.mm"
include "com12.mm"
include "adantl.mm"
include "syl6bi.mm"
include "rexlimdv.mm"
include "imim2d.mm"
include "ralimdv.mm"
include "jctild.mm"
include "adantld.mm"
include "cfil.mm"
include "simpl2.mm"
include "c0.mm"
include "wne.mm"
include "snssd.mm"
include "snnzg.mm"
include "neifil.mm"
include "syl3anc.mm"
include "syl5eqel.mm"
include "isflf.mm"
include "iscnp.mm"
include "adantr.mm"
include "3imtr4d.mm"
include "impr.mm"
include "impbida.mm"

theorem cnpflf2
  let cA: class A
  let cF: class F
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cnpflf2.3: |- L = ( ( nei ` J ) ` { A } )


  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) /\ A e. X ) -> ( F e. ( ( J CnP K ) ` A ) <-> ( F : X --> Y /\ ( F ` A ) e. ( ( K fLimf L ) ` F ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    cA
    cX
    wcel
    #
    w3a
    #
    cF
    cA
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    cX
    cY
    cF
    wf
    #
    cA
    cF
    cfv
    #
    cF
    cK
    cL
    cflf
    co
    cfv
    wcel
    #
    wa
    @3
    @4
    wa
    #
    @5
    @7
    @0
    @1
    @4
    @5
    @2
    @0
    @1
    @4
    @5
    cA
    cF
    cJ
    cK
    cX
    cY
    cnpf2
    3expa
    3adantl3
    @8
    cA
    cJ
    cL
    cflim
    co
    #
    wcel
    #
    @4
    @7
    @8
    @0
    @2
    @10
    @0
    @1
    @2
    @4
    simpl1
    @0
    @1
    @2
    @4
    simpl3
    @0
    @2
    wa
    cA
    cJ
    cA
    csn
    #
    cJ
    cnei
    cfv
    cfv
    #
    cflim
    co
    @9
    cA
    cJ
    cX
    neiflim
    cL
    @12
    cJ
    cflim
    cnpflf2.3
    oveq2i
    syl6eleqr
    syl2anc
    @3
    @4
    simpr
    cA
    cF
    cJ
    cK
    cL
    cnpflfi
    syl2anc
    jca
    @3
    @5
    @7
    @4
    @3
    @5
    wa
    #
    @6
    cY
    wcel
    #
    @6
    vu
    cv
    #
    wcel
    #
    cF
    vz
    cv
    #
    cima
    #
    @15
    wss
    #
    vz
    cL
    wrex
    #
    wi
    #
    vu
    cK
    wral
    #
    wa
    #
    @5
    @16
    cA
    vv
    cv
    #
    wcel
    #
    cF
    @24
    cima
    #
    @15
    wss
    #
    wa
    #
    vv
    cJ
    wrex
    #
    wi
    #
    vu
    cK
    wral
    #
    wa
    #
    @7
    @4
    @13
    @22
    @32
    @14
    @13
    @22
    @31
    @5
    @13
    @21
    @30
    vu
    cK
    @13
    @20
    @29
    @16
    @13
    @19
    @29
    vz
    cL
    @13
    @17
    cL
    wcel
    #
    @17
    cJ
    cuni
    #
    wss
    #
    @25
    @24
    @17
    wss
    #
    wa
    #
    vv
    cJ
    wrex
    #
    wa
    #
    @19
    @29
    wi
    #
    @13
    cJ
    ctop
    wcel
    #
    cA
    @34
    wcel
    #
    @33
    @39
    wb
    @13
    @0
    @41
    @0
    @1
    @2
    @5
    simpl1
    #
    cX
    cJ
    topontop
    syl
    @13
    cA
    cX
    @34
    @0
    @1
    @2
    @5
    simpl3
    #
    @13
    @0
    cX
    @34
    wceq
    @43
    cX
    cJ
    toponuni
    syl
    eleqtrd
    @33
    @17
    @12
    wcel
    @41
    @42
    wa
    @39
    cL
    @12
    @17
    cnpflf2.3
    eleq2i
    cA
    vv
    cJ
    @17
    @34
    @34
    eqid
    isneip
    syl5bb
    syl2anc
    @38
    @40
    @35
    @19
    @38
    @29
    @19
    @37
    @28
    vv
    cJ
    @19
    @36
    @27
    @25
    @26
    @18
    wss
    @19
    @27
    @36
    @26
    @18
    @15
    sstr2
    @24
    @17
    cF
    imass2
    syl11
    anim2d
    reximdv
    com12
    adantl
    syl6bi
    rexlimdv
    imim2d
    ralimdv
    @3
    @5
    simpr
    #
    jctild
    adantld
    @13
    @1
    cL
    cX
    cfil
    cfv
    #
    wcel
    @5
    @7
    @23
    wb
    @0
    @1
    @2
    @5
    simpl2
    @13
    cL
    @12
    @46
    cnpflf2.3
    @13
    @0
    @11
    cX
    wss
    @11
    c0
    wne
    #
    @12
    @46
    wcel
    @43
    @13
    cA
    cX
    @44
    snssd
    @13
    @2
    @47
    @44
    cA
    cX
    snnzg
    syl
    @11
    cJ
    cX
    neifil
    syl3anc
    syl5eqel
    @45
    @6
    vu
    cF
    cK
    cL
    cY
    cX
    vz
    isflf
    syl3anc
    @3
    @4
    @32
    wb
    @5
    vv
    vu
    cA
    cF
    cJ
    cK
    cX
    cY
    iscnp
    adantr
    3imtr4d
    impr
    impbida
end
