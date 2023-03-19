include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell14qr.mm"
include "cfv.mm"
include "wa.mm"
include "clog.mm"
include "cpellfund.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cz.mm"
include "cexp.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "crp.mm"
include "c1.mm"
include "wne.mm"
include "cr.mm"
include "pell14qrrp.mm"
include "pellfundrp.mm"
include "adantr.mm"
include "pellfundne1.mm"
include "reglogcl.mm"
include "syl3anc.mm"
include "flcld.mm"
include "cneg.mm"
include "pell14qrre.mm"
include "recnd.mm"
include "rpexpcld.mm"
include "rpcnd.mm"
include "znegcld.mm"
include "rpne0d.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "simpl.mm"
include "cpell1qr.mm"
include "pell1qrss14.mm"
include "pellfundex.mm"
include "sseldd.mm"
include "pell14qrexpcl.mm"
include "pell14qrmulcl.mm"
include "mpd3an3.mm"
include "cc0.mm"
include "caddc.mm"
include "cmo.mm"
include "1rp.mm"
include "a1i.mm"
include "modge0.mm"
include "syl2anc.mm"
include "cmin.mm"
include "zcnd.mm"
include "negsubd.mm"
include "modfrac.mm"
include "syl.mm"
include "eqtr4d.mm"
include "breqtrrd.mm"
include "reglog1.mm"
include "reglogmul.mm"
include "syl112anc.mm"
include "reglogexpbas.mm"
include "syl12anc.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "3brtr4d.mm"
include "wb.mm"
include "rpmulcld.mm"
include "pellfundgt1.mm"
include "reglogleb.mm"
include "syl22anc.mm"
include "mpbird.mm"
include "modlt.mm"
include "eqbrtrd.mm"
include "reglogbas.mm"
include "reglogltb.mm"
include "pellfund14gap.mm"
include "negidd.mm"
include "cc.mm"
include "expaddz.mm"
include "exp0d.mm"
include "3eqtr3rd.mm"
include "mulcan2ad.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"

theorem pellfund14
  let vx: setvar x
  let cA: class A
  let cD: class D

  disjoint D x
  disjoint A x
  assert |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) -> E. x e. ZZ A = ( ( PellFund ` D ) ^ x ) )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    cA
    cD
    cpell14qr
    cfv
    #
    wcel
    #
    wa
    #
    cA
    clog
    cfv
    cD
    cpellfund
    cfv
    #
    clog
    cfv
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    cz
    wcel
    #
    cA
    @4
    @7
    cexp
    co
    #
    wceq
    #
    cA
    @4
    vx
    cv
    #
    cexp
    co
    #
    wceq
    #
    vx
    cz
    wrex
    @3
    @6
    @3
    cA
    crp
    wcel
    #
    @4
    crp
    wcel
    #
    @4
    c1
    wne
    #
    @6
    cr
    wcel
    #
    cA
    cD
    pell14qrrp
    #
    @0
    @15
    @2
    cD
    pellfundrp
    adantr
    #
    @0
    @16
    @2
    cD
    pellfundne1
    adantr
    #
    cA
    @4
    reglogcl
    syl3anc
    #
    flcld
    #
    @3
    cA
    @9
    @4
    @7
    cneg
    #
    cexp
    co
    #
    @3
    cA
    cA
    cD
    pell14qrre
    recnd
    @3
    @9
    @3
    @4
    @7
    @19
    @22
    rpexpcld
    rpcnd
    @3
    @24
    @3
    @4
    @23
    @19
    @3
    @7
    @22
    znegcld
    #
    rpexpcld
    #
    rpcnd
    @3
    @24
    @26
    rpne0d
    @3
    cA
    @24
    cmul
    co
    #
    c1
    @9
    @24
    cmul
    co
    #
    @3
    @0
    @27
    @1
    wcel
    #
    c1
    @27
    cle
    wbr
    #
    @27
    @4
    clt
    wbr
    #
    @27
    c1
    wceq
    @0
    @2
    simpl
    #
    @0
    @2
    @24
    @1
    wcel
    #
    @29
    @3
    @0
    @4
    @1
    wcel
    #
    @23
    cz
    wcel
    #
    @33
    @32
    @0
    @34
    @2
    @0
    cD
    cpell1qr
    cfv
    @1
    @4
    cD
    pell1qrss14
    cD
    pellfundex
    sseldd
    adantr
    @25
    @4
    @23
    cD
    pell14qrexpcl
    syl3anc
    cA
    @24
    cD
    pell14qrmulcl
    mpd3an3
    @3
    @30
    c1
    clog
    cfv
    @5
    cdiv
    co
    #
    @27
    clog
    cfv
    @5
    cdiv
    co
    #
    cle
    wbr
    #
    @3
    cc0
    @6
    @23
    caddc
    co
    #
    @36
    @37
    cle
    @3
    cc0
    @6
    c1
    cmo
    co
    #
    @39
    cle
    @3
    @17
    c1
    crp
    wcel
    #
    cc0
    @40
    cle
    wbr
    @21
    @41
    @3
    1rp
    a1i
    #
    @6
    c1
    modge0
    syl2anc
    @3
    @39
    @6
    @7
    cmin
    co
    #
    @40
    @3
    @6
    @7
    @3
    @6
    @21
    recnd
    @3
    @7
    @22
    zcnd
    #
    negsubd
    @3
    @17
    @40
    @43
    wceq
    @21
    @6
    modfrac
    syl
    eqtr4d
    #
    breqtrrd
    @3
    @15
    @16
    @36
    cc0
    wceq
    @19
    @20
    @4
    reglog1
    syl2anc
    @3
    @37
    @6
    @24
    clog
    cfv
    @5
    cdiv
    co
    #
    caddc
    co
    #
    @39
    @3
    @14
    @24
    crp
    wcel
    @15
    @16
    @37
    @47
    wceq
    @18
    @26
    @19
    @20
    cA
    @24
    @4
    reglogmul
    syl112anc
    @3
    @46
    @23
    @6
    caddc
    @3
    @35
    @15
    @16
    @46
    @23
    wceq
    @25
    @19
    @20
    @4
    @23
    reglogexpbas
    syl12anc
    oveq2d
    eqtrd
    #
    3brtr4d
    @3
    @41
    @27
    crp
    wcel
    #
    @15
    c1
    @4
    clt
    wbr
    #
    @30
    @38
    wb
    @42
    @3
    cA
    @24
    @18
    @26
    rpmulcld
    #
    @19
    @0
    @50
    @2
    cD
    pellfundgt1
    adantr
    #
    c1
    @27
    @4
    reglogleb
    syl22anc
    mpbird
    @3
    @31
    @37
    @5
    @5
    cdiv
    co
    #
    clt
    wbr
    #
    @3
    @39
    c1
    @37
    @53
    clt
    @3
    @39
    @40
    c1
    clt
    @45
    @3
    @17
    @41
    @40
    c1
    clt
    wbr
    @21
    @42
    @6
    c1
    modlt
    syl2anc
    eqbrtrd
    @48
    @3
    @15
    @16
    @53
    c1
    wceq
    @19
    @20
    @4
    reglogbas
    syl2anc
    3brtr4d
    @3
    @49
    @15
    @15
    @50
    @31
    @54
    wb
    @51
    @19
    @19
    @52
    @27
    @4
    @4
    reglogltb
    syl22anc
    mpbird
    @27
    cD
    pellfund14gap
    syl112anc
    @3
    @4
    @7
    @23
    caddc
    co
    #
    cexp
    co
    #
    @4
    cc0
    cexp
    co
    @28
    c1
    @3
    @55
    cc0
    @4
    cexp
    @3
    @7
    @44
    negidd
    oveq2d
    @3
    @4
    cc
    wcel
    @4
    cc0
    wne
    @8
    @35
    @56
    @28
    wceq
    @3
    @4
    @19
    rpcnd
    #
    @3
    @4
    @19
    rpne0d
    @22
    @25
    @4
    @7
    @23
    expaddz
    syl22anc
    @3
    @4
    @57
    exp0d
    3eqtr3rd
    eqtrd
    mulcan2ad
    @13
    @10
    vx
    @7
    cz
    @11
    @7
    wceq
    @12
    @9
    cA
    @11
    @7
    @4
    cexp
    oveq2
    eqeq2d
    rspcev
    syl2anc
end
