include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cnt.mm"
include "cfv.mm"
include "wf.mm"
include "ccnp.mm"
include "co.mm"
include "cres.mm"
include "crest.mm"
include "wi.mm"
include "cnptop2.mm"
include "a1i.mm"
include "wb.mm"
include "w3a.mm"
include "cv.mm"
include "cima.mm"
include "wrex.mm"
include "wral.mm"
include "wceq.mm"
include "ntrss2.mm"
include "3ad2ant1.mm"
include "simp2l.mm"
include "sseldd.mm"
include "fvres.mm"
include "syl.mm"
include "eqcomd.mm"
include "eleq1d.mm"
include "cin.mm"
include "inss1.mm"
include "imass2.mm"
include "sstr2.mm"
include "mp2b.mm"
include "anim2i.mm"
include "reximi.mm"
include "simp1l.mm"
include "ntropn.mm"
include "inopn.mm"
include "3com23.mm"
include "3expia.mm"
include "syl2anc.mm"
include "elin.mm"
include "simplbi2com.mm"
include "sslin.mm"
include "anim12d.mm"
include "eleq2.mm"
include "imaeq2.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl6.mm"
include "expdimp.mm"
include "rexlimdva.mm"
include "cbvrexv.mm"
include "syl6ib.mm"
include "impbid2.mm"
include "cvv.mm"
include "vex.mm"
include "inex1.mm"
include "cuni.mm"
include "uniexg.mm"
include "simp1r.mm"
include "syl6sseq.mm"
include "ssexd.mm"
include "elrest.mm"
include "rbaib.mm"
include "sylan9bbr.mm"
include "simpr.mm"
include "imaeq2d.mm"
include "inss2.mm"
include "resima2.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "rexxfr2d.mm"
include "bitr4d.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "simp3.mm"
include "iscnp2.mm"
include "baib.mm"
include "syl3anc.mm"
include "simp2r.mm"
include "biantrurd.mm"
include "ctopon.mm"
include "toptopon.mm"
include "sylib.mm"
include "resttopon.mm"
include "iscnp.mm"
include "fssresd.mm"
include "3bitr4d.mm"
include "pm5.21ndd.mm"

theorem cnprest
  let cA: class A
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  assume cnprest.1: |- X = U. J
  assume cnprest.2: |- Y = U. K


  assert |- ( ( ( J e. Top /\ A C_ X ) /\ ( P e. ( ( int ` J ) ` A ) /\ F : X --> Y ) ) -> ( F e. ( ( J CnP K ) ` P ) <-> ( F |` A ) e. ( ( ( J |`t A ) CnP K ) ` P ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cX
    wss
    #
    wa
    #
    cP
    cA
    cJ
    cnt
    cfv
    cfv
    #
    wcel
    #
    cX
    cY
    cF
    wf
    #
    wa
    #
    wa
    #
    cK
    ctop
    wcel
    #
    cF
    cP
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    cF
    cA
    cres
    #
    cP
    cJ
    cA
    crest
    co
    #
    cK
    ccnp
    co
    cfv
    wcel
    #
    @9
    @8
    wi
    @7
    cP
    cF
    cJ
    cK
    cnptop2
    a1i
    @12
    @8
    wi
    @7
    cP
    @10
    @11
    cK
    cnptop2
    a1i
    @2
    @6
    @8
    @9
    @12
    wb
    @2
    @6
    @8
    w3a
    #
    cP
    cF
    cfv
    #
    vy
    cv
    #
    wcel
    #
    cP
    vx
    cv
    #
    wcel
    #
    cF
    @17
    cima
    #
    @15
    wss
    #
    wa
    #
    vx
    cJ
    wrex
    #
    wi
    #
    vy
    cK
    wral
    #
    cP
    @10
    cfv
    #
    @15
    wcel
    #
    cP
    vz
    cv
    #
    wcel
    #
    @10
    @27
    cima
    #
    @15
    wss
    #
    wa
    #
    vz
    @11
    wrex
    #
    wi
    #
    vy
    cK
    wral
    #
    @9
    @12
    @13
    @23
    @33
    vy
    cK
    @13
    @16
    @26
    @22
    @32
    @13
    @14
    @25
    @15
    @13
    @25
    @14
    @13
    cP
    cA
    wcel
    #
    @25
    @14
    wceq
    @13
    @3
    cA
    cP
    @2
    @6
    @3
    cA
    wss
    #
    @8
    cA
    cJ
    cX
    cnprest.1
    ntrss2
    3ad2ant1
    #
    @2
    @4
    @5
    @8
    simp2l
    #
    sseldd
    #
    cP
    cA
    cF
    fvres
    syl
    eqcomd
    eleq1d
    @13
    @22
    @18
    cF
    @17
    cA
    cin
    #
    cima
    #
    @15
    wss
    #
    wa
    #
    vx
    cJ
    wrex
    #
    @32
    @13
    @22
    @44
    @21
    @43
    vx
    cJ
    @20
    @42
    @18
    @40
    @17
    wss
    @41
    @19
    wss
    @20
    @42
    wi
    @17
    cA
    inss1
    @40
    @17
    cF
    imass2
    @41
    @19
    @15
    sstr2
    mp2b
    anim2i
    reximi
    @13
    @44
    @28
    cF
    @27
    cima
    #
    @15
    wss
    #
    wa
    #
    vz
    cJ
    wrex
    #
    @22
    @13
    @43
    @48
    vx
    cJ
    @13
    @17
    cJ
    wcel
    #
    @43
    @48
    @13
    @49
    @43
    wa
    @17
    @3
    cin
    #
    cJ
    wcel
    #
    cP
    @50
    wcel
    #
    cF
    @50
    cima
    #
    @15
    wss
    #
    wa
    #
    wa
    @48
    @13
    @49
    @51
    @43
    @55
    @13
    @0
    @3
    cJ
    wcel
    #
    @49
    @51
    wi
    @0
    @1
    @6
    @8
    simp1l
    #
    @2
    @6
    @56
    @8
    cA
    cJ
    cX
    cnprest.1
    ntropn
    3ad2ant1
    @0
    @56
    @49
    @51
    @0
    @49
    @56
    @51
    @17
    @3
    cJ
    inopn
    3com23
    3expia
    syl2anc
    @13
    @18
    @52
    @42
    @54
    @13
    @4
    @18
    @52
    wi
    @38
    @52
    @18
    @4
    cP
    @17
    @3
    elin
    simplbi2com
    syl
    @13
    @53
    @41
    wss
    #
    @42
    @54
    wi
    @13
    @50
    @40
    wss
    #
    @58
    @13
    @36
    @59
    @37
    @3
    cA
    @17
    sslin
    syl
    @50
    @40
    cF
    imass2
    syl
    @53
    @41
    @15
    sstr2
    syl
    anim12d
    anim12d
    @47
    @55
    vz
    @50
    cJ
    @27
    @50
    wceq
    #
    @28
    @52
    @46
    @54
    @27
    @50
    cP
    eleq2
    @60
    @45
    @53
    @15
    @27
    @50
    cF
    imaeq2
    sseq1d
    anbi12d
    rspcev
    syl6
    expdimp
    rexlimdva
    @47
    @21
    vz
    vx
    cJ
    @27
    @17
    wceq
    #
    @28
    @18
    @46
    @20
    @27
    @17
    cP
    eleq2
    @61
    @45
    @19
    @15
    @27
    @17
    cF
    imaeq2
    sseq1d
    anbi12d
    cbvrexv
    syl6ib
    impbid2
    @13
    @31
    @43
    vz
    vx
    @40
    @11
    cJ
    cvv
    @40
    cvv
    wcel
    @13
    @49
    wa
    @17
    cA
    vx
    vex
    inex1
    a1i
    @13
    @0
    cA
    cvv
    wcel
    @27
    @11
    wcel
    @27
    @40
    wceq
    #
    vx
    cJ
    wrex
    wb
    @57
    @13
    cA
    cJ
    cuni
    #
    cvv
    @13
    @0
    @63
    cvv
    wcel
    @57
    cJ
    ctop
    uniexg
    syl
    @13
    cA
    cX
    @63
    @0
    @1
    @6
    @8
    simp1r
    #
    cnprest.1
    syl6sseq
    ssexd
    vx
    @27
    cA
    cJ
    ctop
    cvv
    elrest
    syl2anc
    @13
    @62
    wa
    #
    @28
    @18
    @30
    @42
    @62
    @28
    cP
    @40
    wcel
    #
    @13
    @18
    @27
    @40
    cP
    eleq2
    @13
    @35
    @66
    @18
    wb
    @39
    @66
    @18
    @35
    cP
    @17
    cA
    elin
    rbaib
    syl
    sylan9bbr
    @65
    @29
    @41
    @15
    @65
    @29
    @10
    @40
    cima
    #
    @41
    @65
    @27
    @40
    @10
    @13
    @62
    simpr
    imaeq2d
    @40
    cA
    wss
    @67
    @41
    wceq
    @17
    cA
    inss2
    cF
    @40
    cA
    resima2
    ax-mp
    syl6eq
    sseq1d
    anbi12d
    rexxfr2d
    bitr4d
    imbi12d
    ralbidv
    @13
    @9
    @5
    @24
    wa
    #
    @24
    @13
    @0
    @8
    cP
    cX
    wcel
    #
    @9
    @68
    wb
    @57
    @2
    @6
    @8
    simp3
    #
    @13
    cA
    cX
    cP
    @64
    @39
    sseldd
    @9
    @0
    @8
    @69
    w3a
    @68
    vx
    vy
    cP
    cF
    cJ
    cK
    cX
    cY
    cnprest.1
    cnprest.2
    iscnp2
    baib
    syl3anc
    @13
    @5
    @24
    @2
    @4
    @5
    @8
    simp2r
    #
    biantrurd
    bitr4d
    @13
    @12
    cA
    cY
    @10
    wf
    #
    @34
    wa
    #
    @34
    @13
    @11
    cA
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
    @35
    @12
    @73
    wb
    @13
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @1
    @74
    @13
    @0
    @76
    @57
    cJ
    cX
    cnprest.1
    toptopon
    sylib
    @64
    cA
    cJ
    cX
    resttopon
    syl2anc
    @13
    @8
    @75
    @70
    cK
    cY
    cnprest.2
    toptopon
    sylib
    @39
    vz
    vy
    cP
    @10
    @11
    cK
    cA
    cY
    iscnp
    syl3anc
    @13
    @72
    @34
    @13
    cX
    cY
    cA
    cF
    @71
    @64
    fssresd
    biantrurd
    bitr4d
    3bitr4d
    3expia
    pm5.21ndd
end
