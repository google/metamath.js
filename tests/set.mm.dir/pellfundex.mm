include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpellfund.mm"
include "cfv.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "clt.mm"
include "wa.mm"
include "cpell1qr.mm"
include "wrex.mm"
include "cr.mm"
include "2re.mm"
include "pellfundre.mm"
include "remulcl.mm"
include "sylancr.mm"
include "caddc.mm"
include "cc0.mm"
include "c1.mm"
include "0red.mm"
include "1red.mm"
include "0lt1.mm"
include "a1i.mm"
include "pellfundgt1.mm"
include "lttrd.mm"
include "elrpd.mm"
include "ltaddrpd.mm"
include "recnd.mm"
include "2timesd.mm"
include "breqtrrd.mm"
include "pellfundglb.mm"
include "mpd3an23.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "adantr.mm"
include "cpell14qr.mm"
include "pell1qrss14.mm"
include "sselda.mm"
include "pell14qrre.mm"
include "syldan.mm"
include "leloed.mm"
include "simp-4l.mm"
include "simp-4r.mm"
include "simplr.mm"
include "simprr.mm"
include "ad3antrrr.mm"
include "ad4antr.mm"
include "wss.mm"
include "sseldd.mm"
include "syl2anc.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "wb.mm"
include "2pos.mm"
include "lemul2.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "ltletrd.mm"
include "w3a.mm"
include "cdiv.mm"
include "simp1.mm"
include "3ad2ant1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "pell14qrdivcl.mm"
include "syl3anc.mm"
include "mulid2d.mm"
include "simp3l.mm"
include "eqbrtrd.mm"
include "pell14qrgt0.mm"
include "ltmuldiv.mm"
include "simp3r.mm"
include "ltdivmul2.mm"
include "mpbird.mm"
include "wn.mm"
include "simpll.mm"
include "pell14qrgapw.mm"
include "ltnsym.mm"
include "mpd.mm"
include "pm2.21dd.mm"
include "syl22anc.mm"
include "syl122anc.mm"
include "r19.29a.mm"
include "exp32.mm"
include "simp2.mm"
include "simp1r.mm"
include "eqeltrd.mm"
include "3exp.mm"
include "jaod.mm"
include "sylbid.mm"
include "impd.mm"
include "rexlimdva.mm"

theorem pellfundex
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cA: class A
  let vx: setvar x


  assert |- ( D e. ( NN \ []NN ) -> ( PellFund ` D ) e. ( Pell1QR ` D ) )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    cD
    cpellfund
    cfv
    #
    va
    cv
    #
    cle
    wbr
    #
    @2
    c2
    @1
    cmul
    co
    #
    clt
    wbr
    #
    wa
    #
    va
    cD
    cpell1qr
    cfv
    #
    wrex
    #
    @1
    @7
    wcel
    #
    @0
    @4
    cr
    wcel
    #
    @1
    @4
    clt
    wbr
    @8
    @0
    c2
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @10
    2re
    cD
    pellfundre
    #
    c2
    @1
    remulcl
    sylancr
    #
    @0
    @1
    @1
    @1
    caddc
    co
    @4
    clt
    @0
    @1
    @1
    @13
    @0
    @1
    @13
    @0
    cc0
    c1
    @1
    @0
    0red
    @0
    1red
    @13
    cc0
    c1
    clt
    wbr
    @0
    0lt1
    a1i
    cD
    pellfundgt1
    lttrd
    elrpd
    ltaddrpd
    @0
    @1
    @0
    @1
    @13
    recnd
    2timesd
    breqtrrd
    va
    @4
    cD
    pellfundglb
    mpd3an23
    @0
    @6
    @9
    va
    @7
    @0
    @2
    @7
    wcel
    #
    wa
    #
    @3
    @5
    @9
    @16
    @3
    @1
    @2
    clt
    wbr
    #
    @1
    @2
    wceq
    #
    wo
    @5
    @9
    wi
    #
    @16
    @1
    @2
    @0
    @12
    @15
    @13
    adantr
    @0
    @15
    @2
    cD
    cpell14qr
    cfv
    #
    wcel
    #
    @2
    cr
    wcel
    #
    @0
    @7
    @20
    @2
    cD
    pell1qrss14
    #
    sselda
    @2
    cD
    pell14qrre
    #
    syldan
    #
    leloed
    @16
    @17
    @19
    @18
    @16
    @17
    @5
    @9
    @16
    @17
    @5
    wa
    #
    wa
    #
    @1
    vb
    cv
    #
    cle
    wbr
    #
    @28
    @2
    clt
    wbr
    #
    wa
    #
    @9
    vb
    @7
    @27
    @28
    @7
    wcel
    #
    wa
    #
    @31
    wa
    #
    @0
    @15
    @32
    @30
    @2
    c2
    @28
    cmul
    co
    #
    clt
    wbr
    #
    @9
    @0
    @15
    @26
    @32
    @31
    simp-4l
    #
    @0
    @15
    @26
    @32
    @31
    simp-4r
    @27
    @32
    @31
    simplr
    #
    @33
    @29
    @30
    simprr
    @34
    @2
    @4
    @35
    @16
    @22
    @26
    @32
    @31
    @25
    ad3antrrr
    @0
    @10
    @15
    @26
    @32
    @31
    @14
    ad4antr
    @34
    @11
    @28
    cr
    wcel
    #
    @35
    cr
    wcel
    2re
    @34
    @0
    @28
    @20
    wcel
    #
    @39
    @37
    @34
    @7
    @20
    @28
    @0
    @7
    @20
    wss
    #
    @15
    @26
    @32
    @31
    @23
    ad4antr
    @38
    sseldd
    @28
    cD
    pell14qrre
    #
    syl2anc
    #
    c2
    @28
    remulcl
    sylancr
    @27
    @5
    @32
    @31
    @16
    @17
    @5
    simprr
    ad2antrr
    @34
    @29
    @4
    @35
    cle
    wbr
    #
    @33
    @29
    @30
    simprl
    @34
    @12
    @39
    @11
    cc0
    c2
    clt
    wbr
    #
    @29
    @44
    wb
    @0
    @12
    @15
    @26
    @32
    @31
    @13
    ad4antr
    @43
    @11
    @34
    2re
    a1i
    @45
    @34
    2pos
    a1i
    @1
    @28
    c2
    lemul2
    syl112anc
    mpbid
    ltletrd
    @0
    @15
    @32
    wa
    #
    @30
    @36
    wa
    #
    w3a
    #
    @0
    @2
    @28
    cdiv
    co
    #
    @20
    wcel
    #
    c1
    @49
    clt
    wbr
    #
    @49
    c2
    clt
    wbr
    #
    @9
    @0
    @46
    @47
    simp1
    #
    @48
    @0
    @21
    @40
    @50
    @53
    @48
    @7
    @20
    @2
    @0
    @46
    @41
    @47
    @23
    3ad2ant1
    #
    @0
    @15
    @32
    @47
    simp2l
    sseldd
    #
    @48
    @7
    @20
    @28
    @54
    @0
    @15
    @32
    @47
    simp2r
    sseldd
    #
    @2
    @28
    cD
    pell14qrdivcl
    syl3anc
    @48
    c1
    @28
    cmul
    co
    #
    @2
    clt
    wbr
    #
    @51
    @48
    @57
    @28
    @2
    clt
    @48
    @28
    @48
    @28
    @48
    @0
    @40
    @39
    @53
    @56
    @42
    syl2anc
    #
    recnd
    mulid2d
    @0
    @46
    @30
    @36
    simp3l
    eqbrtrd
    @48
    c1
    cr
    wcel
    @22
    @39
    cc0
    @28
    clt
    wbr
    #
    @58
    @51
    wb
    @48
    1red
    @48
    @0
    @21
    @22
    @53
    @55
    @24
    syl2anc
    #
    @59
    @48
    @0
    @40
    @60
    @53
    @56
    @28
    cD
    pell14qrgt0
    syl2anc
    #
    c1
    @2
    @28
    ltmuldiv
    syl112anc
    mpbid
    @48
    @52
    @36
    @0
    @46
    @30
    @36
    simp3r
    @48
    @22
    @11
    @39
    @60
    @52
    @36
    wb
    @61
    @11
    @48
    2re
    a1i
    @59
    @62
    @2
    c2
    @28
    ltdivmul2
    syl112anc
    mpbird
    @0
    @50
    wa
    #
    @51
    @52
    wa
    #
    wa
    #
    @52
    @9
    @63
    @51
    @52
    simprr
    @65
    c2
    @49
    clt
    wbr
    #
    @52
    wn
    #
    @65
    @0
    @50
    @51
    @66
    @0
    @50
    @64
    simpll
    @0
    @50
    @64
    simplr
    @63
    @51
    @52
    simprl
    @49
    cD
    pell14qrgapw
    syl3anc
    @65
    @11
    @49
    cr
    wcel
    #
    @66
    @67
    wi
    2re
    @63
    @68
    @64
    @49
    cD
    pell14qrre
    adantr
    c2
    @49
    ltnsym
    sylancr
    mpd
    pm2.21dd
    syl22anc
    syl122anc
    @27
    @0
    @22
    @17
    @31
    vb
    @7
    wrex
    @0
    @15
    @26
    simpll
    @16
    @22
    @26
    @25
    adantr
    @16
    @17
    @5
    simprl
    vb
    @2
    cD
    pellfundglb
    syl3anc
    r19.29a
    exp32
    @16
    @18
    @5
    @9
    @16
    @18
    @5
    w3a
    @1
    @2
    @7
    @16
    @18
    @5
    simp2
    @0
    @15
    @18
    @5
    simp1r
    eqeltrd
    3exp
    jaod
    sylbid
    impd
    rexlimdva
    mpd
end
