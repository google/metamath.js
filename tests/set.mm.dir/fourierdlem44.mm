include "cpi.mm"
include "cneg.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "c2.mm"
include "cdiv.mm"
include "csin.mm"
include "cfv.mm"
include "cmul.mm"
include "cioo.mm"
include "cxr.mm"
include "0xr.mm"
include "a1i.mm"
include "2re.mm"
include "pire.mm"
include "remulcli.mm"
include "rexri.mm"
include "cr.mm"
include "renegcli.mm"
include "id.mm"
include "eliccre.mm"
include "syl3anc.mm"
include "adantr.mm"
include "simpr.mm"
include "cle.mm"
include "rexrd.mm"
include "iccleub.mm"
include "crp.mm"
include "pirp.mm"
include "2timesgt.mm"
include "ax-mp.mm"
include "lelttrd.mm"
include "eliood.mm"
include "adantlr.mm"
include "sinaover2ne0.mm"
include "syl.mm"
include "wn.mm"
include "simpll.mm"
include "0red.mm"
include "simplr.mm"
include "lttri5d.mm"
include "wceq.mm"
include "cc.mm"
include "recnd.mm"
include "halfcld.mm"
include "sinneg.mm"
include "2cnd.mm"
include "2ne0.mm"
include "divnegd.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "renegcld.mm"
include "lt0neg1d.mm"
include "mpbid.mm"
include "ltnegi.mm"
include "mpbi.mm"
include "iccgelb.mm"
include "ltletrd.mm"
include "ltnegd.mm"
include "negnegd.mm"
include "breqtrd.mm"
include "eqnetrd.mm"
include "neneqd.mm"
include "sincld.mm"
include "negeq0d.mm"
include "mtbird.mm"
include "neqned.mm"
include "syl2anc.mm"
include "pm2.61dan.mm"

theorem fourierdlem44
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. ( -u _pi [,] _pi ) /\ A =/= 0 ) -> ( sin ` ( A / 2 ) ) =/= 0 )

  proof
    cA
    cpi
    cneg
    #
    cpi
    cicc
    co
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cc0
    cA
    clt
    wbr
    #
    cA
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cc0
    wne
    #
    @3
    @4
    wa
    cA
    cc0
    c2
    cpi
    cmul
    co
    #
    cioo
    co
    #
    wcel
    #
    @7
    @1
    @4
    @10
    @2
    @1
    @4
    wa
    #
    cc0
    @8
    cA
    cc0
    cxr
    wcel
    #
    @11
    0xr
    a1i
    @8
    cxr
    wcel
    #
    @11
    @8
    c2
    cpi
    2re
    pire
    remulcli
    #
    rexri
    #
    a1i
    @1
    cA
    cr
    wcel
    #
    @4
    @1
    @0
    cr
    wcel
    #
    cpi
    cr
    wcel
    #
    @1
    @16
    @17
    @1
    cpi
    pire
    renegcli
    #
    a1i
    #
    @18
    @1
    pire
    a1i
    #
    @1
    id
    #
    @0
    cpi
    cA
    eliccre
    syl3anc
    #
    adantr
    @1
    @4
    simpr
    @1
    cA
    @8
    clt
    wbr
    @4
    @1
    cA
    cpi
    @8
    @23
    @21
    @8
    cr
    wcel
    @1
    @14
    a1i
    #
    @1
    @0
    cxr
    wcel
    #
    cpi
    cxr
    wcel
    #
    @1
    cA
    cpi
    cle
    wbr
    @1
    @0
    @20
    rexrd
    #
    @1
    cpi
    @21
    rexrd
    #
    @22
    @0
    cpi
    cA
    iccleub
    syl3anc
    cpi
    @8
    clt
    wbr
    #
    @1
    cpi
    crp
    wcel
    @29
    pirp
    cpi
    2timesgt
    ax-mp
    #
    a1i
    lelttrd
    adantr
    eliood
    adantlr
    cA
    sinaover2ne0
    syl
    @3
    @4
    wn
    #
    wa
    #
    @1
    cA
    cc0
    clt
    wbr
    #
    @7
    @1
    @2
    @31
    simpll
    #
    @32
    cA
    cc0
    @32
    @1
    @16
    @34
    @23
    syl
    @32
    0red
    @1
    @2
    @31
    simplr
    @3
    @31
    simpr
    lttri5d
    @1
    @33
    wa
    #
    @6
    cc0
    @35
    @6
    cc0
    wceq
    @6
    cneg
    #
    cc0
    wceq
    @35
    @36
    cc0
    @35
    @36
    cA
    cneg
    #
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cc0
    @1
    @36
    @39
    wceq
    @33
    @1
    @5
    cneg
    #
    csin
    cfv
    #
    @36
    @39
    @1
    @5
    cc
    wcel
    @41
    @36
    wceq
    @1
    cA
    @1
    cA
    @23
    recnd
    #
    halfcld
    #
    @5
    sinneg
    syl
    @1
    @40
    @38
    csin
    @1
    cA
    c2
    @42
    @1
    2cnd
    c2
    cc0
    wne
    @1
    2ne0
    a1i
    divnegd
    fveq2d
    eqtr3d
    adantr
    @35
    @37
    @9
    wcel
    @39
    cc0
    wne
    @35
    cc0
    @8
    @37
    @12
    @35
    0xr
    a1i
    @13
    @35
    @15
    a1i
    @1
    @37
    cr
    wcel
    @33
    @1
    cA
    @23
    renegcld
    adantr
    @35
    @33
    cc0
    @37
    clt
    wbr
    @1
    @33
    simpr
    @35
    cA
    @1
    @16
    @33
    @23
    adantr
    #
    lt0neg1d
    mpbid
    @35
    @37
    @8
    cneg
    #
    cneg
    #
    @8
    clt
    @35
    @45
    cA
    clt
    wbr
    @37
    @46
    clt
    wbr
    @35
    @45
    @0
    cA
    @45
    cr
    wcel
    @35
    @8
    @14
    renegcli
    a1i
    #
    @17
    @35
    @19
    a1i
    @44
    @45
    @0
    clt
    wbr
    #
    @35
    @29
    @48
    @30
    cpi
    @8
    pire
    @14
    ltnegi
    mpbi
    a1i
    @1
    @0
    cA
    cle
    wbr
    #
    @33
    @1
    @25
    @26
    @1
    @49
    @27
    @28
    @22
    @0
    cpi
    cA
    iccgelb
    syl3anc
    adantr
    ltletrd
    @35
    @45
    cA
    @47
    @44
    ltnegd
    mpbid
    @1
    @46
    @8
    wceq
    @33
    @1
    @8
    @1
    @8
    @24
    recnd
    negnegd
    adantr
    breqtrd
    eliood
    @37
    sinaover2ne0
    syl
    eqnetrd
    neneqd
    @35
    @6
    @1
    @6
    cc
    wcel
    @33
    @1
    @5
    @43
    sincld
    adantr
    negeq0d
    mtbird
    neqned
    syl2anc
    pm2.61dan
end
