include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c1.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "clt.mm"
include "wo.mm"
include "wb.mm"
include "0re.mm"
include "leloe.mm"
include "mpan.mm"
include "crp.mm"
include "elrp.mm"
include "01sqrex.mm"
include "rprege0.mm"
include "anim1i.mm"
include "anass.mm"
include "sylib.mm"
include "adantrl.mm"
include "reximi2.mm"
include "syl.mm"
include "sylanbr.mm"
include "exp31.mm"
include "sq0.mm"
include "id.mm"
include "syl5eq.mm"
include "0le0.mm"
include "jctil.mm"
include "breq2.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "sylancr.mm"
include "a1d.mm"
include "a1i.mm"
include "jaod.mm"
include "sylbid.mm"
include "imp.mm"
include "cdiv.mm"
include "0lt1.mm"
include "1re.mm"
include "ltletr.mm"
include "mp3an12.mm"
include "mpani.mm"
include "biimpri.mm"
include "syldan.mm"
include "rpreccld.mm"
include "simpr.mm"
include "lerec.mm"
include "mpanl12.mm"
include "mpbid.mm"
include "1div1e1.mm"
include "syl6breq.mm"
include "syl2anc.mm"
include "w3a.mm"
include "rpre.mm"
include "3ad2ant2.mm"
include "rpgt0.mm"
include "wne.mm"
include "gt0ne0.mm"
include "rereccl.mm"
include "recgt0.mm"
include "ltle.mm"
include "sylc.mm"
include "cc.mm"
include "recn.mm"
include "adantr.mm"
include "sqrecd.mm"
include "simp3r.mm"
include "oveq2d.mm"
include "recrec.mm"
include "sylan.mm"
include "3ad2ant1.mm"
include "3eqtrd.mm"
include "syl12anc.mm"
include "rexlimdv3a.mm"
include "mpd.mm"
include "ex.mm"
include "simpl.mm"
include "letric.mm"
include "sylancl.mm"
include "mpjaod.mm"

theorem resqrex
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( ( A e. RR /\ 0 <_ A ) -> E. x e. RR ( 0 <_ x /\ ( x ^ 2 ) = A ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cA
    c1
    cle
    wbr
    #
    cc0
    vx
    cv
    #
    cle
    wbr
    #
    @4
    c2
    cexp
    co
    #
    cA
    wceq
    #
    wa
    #
    vx
    cr
    wrex
    #
    c1
    cA
    cle
    wbr
    #
    @0
    @1
    @3
    @9
    wi
    #
    @0
    @1
    cc0
    cA
    clt
    wbr
    #
    cc0
    cA
    wceq
    #
    wo
    #
    @11
    cc0
    cr
    wcel
    #
    @0
    @1
    @14
    wb
    0re
    cc0
    cA
    leloe
    mpan
    @0
    @12
    @11
    @13
    @0
    @12
    @3
    @9
    @0
    @12
    wa
    #
    cA
    crp
    wcel
    #
    @3
    @9
    cA
    elrp
    #
    @17
    @3
    wa
    @4
    c1
    cle
    wbr
    #
    @7
    wa
    #
    vx
    crp
    wrex
    @9
    vx
    cA
    01sqrex
    @20
    @8
    vx
    crp
    cr
    @4
    crp
    wcel
    #
    @7
    @4
    cr
    wcel
    #
    @8
    wa
    #
    @19
    @21
    @7
    wa
    @22
    @5
    wa
    #
    @7
    wa
    @23
    @21
    @24
    @7
    @4
    rprege0
    anim1i
    @22
    @5
    @7
    anass
    sylib
    adantrl
    reximi2
    syl
    sylanbr
    exp31
    @13
    @11
    wi
    @0
    @13
    @9
    @3
    @13
    @15
    cc0
    cc0
    cle
    wbr
    #
    cc0
    c2
    cexp
    co
    #
    cA
    wceq
    #
    wa
    #
    @9
    0re
    @13
    @27
    @25
    @13
    @26
    cc0
    cA
    sq0
    @13
    id
    syl5eq
    0le0
    jctil
    @8
    @28
    vx
    cc0
    cr
    @4
    cc0
    wceq
    #
    @5
    @25
    @7
    @27
    @4
    cc0
    cc0
    cle
    breq2
    @29
    @6
    @26
    cA
    @4
    cc0
    c2
    cexp
    oveq1
    eqeq1d
    anbi12d
    rspcev
    sylancr
    a1d
    a1i
    jaod
    sylbid
    imp
    @0
    @10
    @9
    wi
    @1
    @0
    @10
    @9
    @0
    @10
    wa
    #
    vy
    cv
    #
    c1
    cle
    wbr
    #
    @31
    c2
    cexp
    co
    #
    c1
    cA
    cdiv
    co
    #
    wceq
    #
    wa
    #
    vy
    crp
    wrex
    #
    @9
    @30
    @34
    crp
    wcel
    @34
    c1
    cle
    wbr
    @37
    @30
    cA
    @0
    @10
    @12
    @17
    @0
    @10
    @12
    @0
    cc0
    c1
    clt
    wbr
    #
    @10
    @12
    0lt1
    @15
    c1
    cr
    wcel
    #
    @0
    @38
    @10
    wa
    @12
    wi
    0re
    1re
    cc0
    c1
    cA
    ltletr
    mp3an12
    mpani
    imp
    #
    @17
    @16
    @18
    biimpri
    syldan
    rpreccld
    @30
    @34
    c1
    c1
    cdiv
    co
    #
    c1
    cle
    @30
    @10
    @34
    @41
    cle
    wbr
    #
    @0
    @10
    simpr
    @0
    @10
    @12
    @10
    @42
    wb
    #
    @40
    @39
    @38
    @16
    @43
    1re
    0lt1
    c1
    cA
    lerec
    mpanl12
    syldan
    mpbid
    1div1e1
    syl6breq
    vy
    @34
    01sqrex
    syl2anc
    @30
    @36
    @9
    vy
    crp
    @30
    @31
    crp
    wcel
    #
    @36
    w3a
    #
    c1
    @31
    cdiv
    co
    #
    cr
    wcel
    #
    cc0
    @46
    cle
    wbr
    #
    @46
    c2
    cexp
    co
    #
    cA
    wceq
    #
    @9
    @45
    @31
    cr
    wcel
    #
    cc0
    @31
    clt
    wbr
    #
    @47
    @44
    @30
    @51
    @36
    @31
    rpre
    3ad2ant2
    #
    @44
    @30
    @52
    @36
    @31
    rpgt0
    3ad2ant2
    #
    @51
    @52
    @31
    cc0
    wne
    @47
    @31
    gt0ne0
    #
    @31
    rereccl
    syldan
    #
    syl2anc
    @45
    @51
    @52
    @48
    @53
    @54
    @51
    @52
    wa
    #
    @47
    cc0
    @46
    clt
    wbr
    #
    @48
    @56
    @31
    recgt0
    @15
    @47
    @58
    @48
    wi
    0re
    cc0
    @46
    ltle
    mpan
    sylc
    syl2anc
    @45
    @49
    c1
    @33
    cdiv
    co
    #
    c1
    @34
    cdiv
    co
    #
    cA
    @45
    @51
    @52
    @49
    @59
    wceq
    @53
    @54
    @57
    @31
    @51
    @31
    cc
    wcel
    @52
    @31
    recn
    adantr
    @55
    sqrecd
    syl2anc
    @45
    @33
    @34
    c1
    cdiv
    @30
    @44
    @32
    @35
    simp3r
    oveq2d
    @30
    @44
    @60
    cA
    wceq
    #
    @36
    @0
    @10
    cA
    cc0
    wne
    #
    @61
    @0
    @10
    @12
    @62
    @40
    cA
    gt0ne0
    syldan
    @0
    cA
    cc
    wcel
    @62
    @61
    cA
    recn
    cA
    recrec
    sylan
    syldan
    3ad2ant1
    3eqtrd
    @8
    @48
    @50
    wa
    vx
    @46
    cr
    @4
    @46
    wceq
    #
    @5
    @48
    @7
    @50
    @4
    @46
    cc0
    cle
    breq2
    @63
    @6
    @49
    cA
    @4
    @46
    c2
    cexp
    oveq1
    eqeq1d
    anbi12d
    rspcev
    syl12anc
    rexlimdv3a
    mpd
    ex
    adantr
    @2
    @0
    @39
    @3
    @10
    wo
    @0
    @1
    simpl
    1re
    cA
    c1
    letric
    sylancl
    mpjaod
end
