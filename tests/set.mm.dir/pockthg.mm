include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cdvds.mm"
include "wn.mm"
include "wi.mm"
include "cprime.mm"
include "wral.mm"
include "cmul.mm"
include "c1.mm"
include "caddc.mm"
include "cn.mm"
include "nnmulcld.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "eluzp1p1.mm"
include "syl.mm"
include "df-2.mm"
include "fveq2i.mm"
include "syl6eleqr.mm"
include "eqeltrd.mm"
include "wa.mm"
include "clt.mm"
include "cr.mm"
include "eluzelre.mm"
include "adantr.mm"
include "nnred.mm"
include "resqcld.mm"
include "prmnn.mm"
include "ad2antrl.mm"
include "cc0.mm"
include "wb.mm"
include "nngt0d.mm"
include "ltmul2.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "nnltp1le.mm"
include "syl2anc.mm"
include "nncnd.mm"
include "sqvald.mm"
include "3brtr4d.mm"
include "cmin.mm"
include "cpc.mm"
include "cmo.mm"
include "wceq.mm"
include "cdiv.mm"
include "cgcd.mm"
include "cz.mm"
include "wrex.mm"
include "exp1d.mm"
include "nnge1.mm"
include "ad2antll.mm"
include "cn0.mm"
include "simprl.mm"
include "nnzd.mm"
include "ad2antrr.mm"
include "1nn0.mm"
include "a1i.mm"
include "pcdvdsb.mm"
include "syl3anc.mm"
include "eqbrtrrd.mm"
include "w3a.mm"
include "simpl1.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "simpl3l.mm"
include "simpl3r.mm"
include "simprrl.mm"
include "simprrr.mm"
include "pockthlem.mm"
include "rexlimdvaa.mm"
include "3expa.mm"
include "embantd.mm"
include "expr.mm"
include "id.mm"
include "prmuz2.mm"
include "uz2m1nn.mm"
include "pccl.mm"
include "syl2anr.mm"
include "nn0ge0d.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "a1dd.mm"
include "wo.mm"
include "simpr.mm"
include "pccld.mm"
include "elnn0.mm"
include "sylib.mm"
include "mpjaod.mm"
include "ralimdva.mm"
include "mpd.mm"
include "pc2dvds.mm"
include "mpbird.mm"
include "dvdsle.mm"
include "nnnn0d.mm"
include "nn0ltlem1.mm"
include "lt2sqd.mm"
include "lelttrd.mm"
include "ltnled.mm"
include "con2d.mm"
include "ralrimiva.mm"
include "isprm5.mm"
include "sylanbrc.mm"

theorem pockthg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cN: class N
  let vp: setvar p
  let vq: setvar q
  assume pockthg.1: |- ( ph -> A e. NN )
  assume pockthg.2: |- ( ph -> B e. NN )
  assume pockthg.3: |- ( ph -> B < A )
  assume pockthg.4: |- ( ph -> N = ( ( A x. B ) + 1 ) )
  assume pockthg.5: |- ( ph -> A. p e. Prime ( p || A -> E. x e. ZZ ( ( ( x ^ ( N - 1 ) ) mod N ) = 1 /\ ( ( ( x ^ ( ( N - 1 ) / p ) ) - 1 ) gcd N ) = 1 ) ) )

  disjoint p x
  disjoint N p
  disjoint N x
  disjoint A p
  disjoint A x
  disjoint p ph
  disjoint ph x
  disjoint p q
  disjoint q x
  disjoint N q
  disjoint ph q
  assert |- ( ph -> N e. Prime )

  proof
    wph
    cN
    c2
    cuz
    cfv
    #
    wcel
    #
    vq
    cv
    #
    c2
    cexp
    co
    #
    cN
    cle
    wbr
    #
    @2
    cN
    cdvds
    wbr
    #
    wn
    wi
    #
    vq
    cprime
    wral
    cN
    cprime
    wcel
    wph
    cN
    cA
    cB
    cmul
    co
    #
    c1
    caddc
    co
    #
    @0
    pockthg.4
    wph
    @8
    c1
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    @0
    wph
    @7
    c1
    cuz
    cfv
    #
    wcel
    @8
    @10
    wcel
    wph
    @7
    cn
    @11
    wph
    cA
    cB
    pockthg.1
    pockthg.2
    nnmulcld
    #
    nnuz
    syl6eleq
    c1
    @7
    eluzp1p1
    syl
    c2
    @9
    cuz
    df-2
    fveq2i
    syl6eleqr
    eqeltrd
    #
    wph
    @6
    vq
    cprime
    wph
    @2
    cprime
    wcel
    #
    wa
    @5
    @4
    wph
    @14
    @5
    @4
    wn
    #
    wph
    @14
    @5
    wa
    #
    wa
    #
    cN
    @3
    clt
    wbr
    @15
    @17
    cN
    cA
    c2
    cexp
    co
    #
    @3
    wph
    cN
    cr
    wcel
    #
    @16
    wph
    @1
    @19
    @13
    c2
    cN
    eluzelre
    syl
    adantr
    #
    wph
    @18
    cr
    wcel
    @16
    wph
    cA
    wph
    cA
    pockthg.1
    nnred
    #
    resqcld
    adantr
    @17
    @2
    @17
    @2
    @14
    @2
    cn
    wcel
    wph
    @5
    @2
    prmnn
    ad2antrl
    #
    nnred
    #
    resqcld
    #
    wph
    cN
    @18
    cle
    wbr
    @16
    wph
    @8
    cA
    cA
    cmul
    co
    #
    cN
    @18
    cle
    wph
    @7
    @25
    clt
    wbr
    #
    @8
    @25
    cle
    wbr
    #
    wph
    cB
    cA
    clt
    wbr
    #
    @26
    pockthg.3
    wph
    cB
    cr
    wcel
    cA
    cr
    wcel
    #
    @29
    cc0
    cA
    clt
    wbr
    @28
    @26
    wb
    wph
    cB
    pockthg.2
    nnred
    @21
    @21
    wph
    cA
    pockthg.1
    nngt0d
    cB
    cA
    cA
    ltmul2
    syl112anc
    mpbid
    wph
    @7
    cn
    wcel
    @25
    cn
    wcel
    @26
    @27
    wb
    @12
    wph
    cA
    cA
    pockthg.1
    pockthg.1
    nnmulcld
    @7
    @25
    nnltp1le
    syl2anc
    mpbid
    pockthg.4
    wph
    cA
    wph
    cA
    pockthg.1
    nncnd
    sqvald
    3brtr4d
    adantr
    @17
    cA
    @2
    clt
    wbr
    #
    @18
    @3
    clt
    wbr
    @17
    @30
    cA
    @2
    c1
    cmin
    co
    #
    cle
    wbr
    #
    @17
    cA
    @31
    cdvds
    wbr
    #
    @32
    @17
    @33
    vp
    cv
    #
    cA
    cpc
    co
    #
    @34
    @31
    cpc
    co
    #
    cle
    wbr
    #
    vp
    cprime
    wral
    #
    @17
    @34
    cA
    cdvds
    wbr
    #
    vx
    cv
    #
    cN
    c1
    cmin
    co
    #
    cexp
    co
    cN
    cmo
    co
    c1
    wceq
    #
    @40
    @41
    @34
    cdiv
    co
    cexp
    co
    c1
    cmin
    co
    cN
    cgcd
    co
    c1
    wceq
    #
    wa
    #
    vx
    cz
    wrex
    #
    wi
    #
    vp
    cprime
    wral
    #
    @38
    wph
    @47
    @16
    pockthg.5
    adantr
    @17
    @46
    @37
    vp
    cprime
    @17
    @34
    cprime
    wcel
    #
    wa
    #
    @35
    cn
    wcel
    #
    @46
    @37
    wi
    #
    @35
    cc0
    wceq
    #
    @17
    @48
    @50
    @51
    @17
    @48
    @50
    wa
    #
    wa
    #
    @39
    @45
    @37
    @54
    @34
    c1
    cexp
    co
    #
    @34
    cA
    cdvds
    @54
    @34
    @54
    @34
    @48
    @34
    cn
    wcel
    @17
    @50
    @34
    prmnn
    ad2antrl
    nncnd
    exp1d
    @54
    c1
    @35
    cle
    wbr
    #
    @55
    cA
    cdvds
    wbr
    #
    @50
    @56
    @17
    @48
    @35
    nnge1
    ad2antll
    @54
    @48
    cA
    cz
    wcel
    #
    c1
    cn0
    wcel
    #
    @56
    @57
    wb
    @17
    @48
    @50
    simprl
    wph
    @58
    @16
    @53
    wph
    cA
    pockthg.1
    nnzd
    #
    ad2antrr
    @59
    @54
    1nn0
    a1i
    c1
    @34
    cA
    pcdvdsb
    syl3anc
    mpbid
    eqbrtrrd
    wph
    @16
    @53
    @45
    @37
    wi
    wph
    @16
    @53
    w3a
    #
    @44
    @37
    vx
    cz
    @61
    @40
    cz
    wcel
    #
    @44
    wa
    #
    wa
    #
    cA
    cB
    @40
    @2
    @34
    cN
    @64
    wph
    cA
    cn
    wcel
    #
    wph
    @16
    @53
    @63
    simpl1
    #
    pockthg.1
    syl
    @64
    wph
    cB
    cn
    wcel
    @66
    pockthg.2
    syl
    @64
    wph
    @28
    @66
    pockthg.3
    syl
    @64
    wph
    cN
    @8
    wceq
    @66
    pockthg.4
    syl
    @14
    @5
    wph
    @53
    @63
    simpl2l
    @14
    @5
    wph
    @53
    @63
    simpl2r
    @48
    @50
    wph
    @16
    @63
    simpl3l
    @48
    @50
    wph
    @16
    @63
    simpl3r
    @61
    @62
    @44
    simprl
    @61
    @62
    @42
    @43
    simprrl
    @61
    @62
    @42
    @43
    simprrr
    pockthlem
    rexlimdvaa
    3expa
    embantd
    expr
    @49
    @52
    @37
    @46
    @49
    @37
    @52
    cc0
    @36
    cle
    wbr
    @49
    @36
    @48
    @48
    @31
    cn
    wcel
    #
    @36
    cn0
    wcel
    @17
    @48
    id
    @14
    @67
    wph
    @5
    @14
    @2
    @0
    wcel
    @67
    @2
    prmuz2
    @2
    uz2m1nn
    syl
    ad2antrl
    #
    @34
    @31
    pccl
    syl2anr
    nn0ge0d
    @35
    cc0
    @36
    cle
    breq1
    syl5ibrcom
    a1dd
    @49
    @35
    cn0
    wcel
    @50
    @52
    wo
    @49
    @34
    cA
    @17
    @48
    simpr
    wph
    @65
    @16
    @48
    pockthg.1
    ad2antrr
    pccld
    @35
    elnn0
    sylib
    mpjaod
    ralimdva
    mpd
    @17
    @58
    @31
    cz
    wcel
    @33
    @38
    wb
    wph
    @58
    @16
    @60
    adantr
    #
    @17
    @31
    @68
    nnzd
    cA
    @31
    vp
    pc2dvds
    syl2anc
    mpbird
    @17
    @58
    @67
    @33
    @32
    wi
    @69
    @68
    cA
    @31
    dvdsle
    syl2anc
    mpd
    @17
    cA
    cn0
    wcel
    #
    @2
    cn0
    wcel
    @30
    @32
    wb
    wph
    @70
    @16
    wph
    cA
    pockthg.1
    nnnn0d
    #
    adantr
    @17
    @2
    @22
    nnnn0d
    #
    cA
    @2
    nn0ltlem1
    syl2anc
    mpbird
    @17
    cA
    @2
    wph
    @29
    @16
    @21
    adantr
    @23
    wph
    cc0
    cA
    cle
    wbr
    @16
    wph
    cA
    @71
    nn0ge0d
    adantr
    @17
    @2
    @72
    nn0ge0d
    lt2sqd
    mpbid
    lelttrd
    @17
    cN
    @3
    @20
    @24
    ltnled
    mpbid
    expr
    con2d
    ralrimiva
    vq
    cN
    isprm5
    sylanbrc
end
