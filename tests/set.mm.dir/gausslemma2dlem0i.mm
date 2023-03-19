include "c2.mm"
include "clgs.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "cc0.mm"
include "ctp.mm"
include "wcel.mm"
include "cmo.mm"
include "cexp.mm"
include "wceq.mm"
include "wi.mm"
include "cz.mm"
include "2z.mm"
include "cprime.mm"
include "csn.mm"
include "cdif.mm"
include "id.mm"
include "gausslemma2dlem0a.mm"
include "nnzd.mm"
include "syl.mm"
include "lgscl1.mm"
include "sylancr.mm"
include "w3o.mm"
include "ovex.mm"
include "eltp.mm"
include "cpr.mm"
include "gausslemma2dlem0h.mm"
include "nn0zd.mm"
include "m1expcl2.mm"
include "wo.mm"
include "elpr.mm"
include "eqcom.mm"
include "biimpi.mm"
include "2a1d.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "eldifi.mm"
include "prmnn.mm"
include "nnred.mm"
include "prmgt1.mm"
include "jca.mm"
include "1mod.mm"
include "3syl.mm"
include "eqeq2d.mm"
include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "oddprmge3.mm"
include "m1modge3gt1.mm"
include "breq2.mm"
include "1re.mm"
include "ltnri.mm"
include "pm2.21i.mm"
include "syl6bi.mm"
include "com12.mm"
include "sylbid.mm"
include "oveq1.mm"
include "eqeq2.mm"
include "imbi12d.mm"
include "syl5ibr.mm"
include "jaoi.mm"
include "sylbi.mm"
include "mpcom.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "crp.mm"
include "nnrpd.mm"
include "0mod.mm"
include "wb.mm"
include "adantr.mm"
include "negmod0.mm"
include "syl6bb.mm"
include "wne.mm"
include "ax-1ne0.mm"
include "eqneqall.mm"
include "mpi.mm"
include "sylbird.mm"
include "adantl.mm"
include "ex.mm"
include "syl5bb.mm"
include "3imtr4g.mm"
include "3jaoi.mm"

theorem gausslemma2dlem0i
  let wph: wff ph
  let cP: class P
  let cH: class H
  let cM: class M
  let cN: class N
  assume gausslemma2dlem0.p: |- ( ph -> P e. ( Prime \ { 2 } ) )
  assume gausslemma2dlem0.m: |- M = ( |_ ` ( P / 4 ) )
  assume gausslemma2dlem0.h: |- H = ( ( P - 1 ) / 2 )
  assume gausslemma2dlem0.n: |- N = ( H - M )


  assert |- ( ph -> ( ( ( 2 /L P ) mod P ) = ( ( -u 1 ^ N ) mod P ) -> ( 2 /L P ) = ( -u 1 ^ N ) ) )

  proof
    c2
    cP
    clgs
    co
    #
    c1
    cneg
    #
    cc0
    c1
    ctp
    wcel
    #
    wph
    @0
    cP
    cmo
    co
    #
    @1
    cN
    cexp
    co
    #
    cP
    cmo
    co
    #
    wceq
    #
    @0
    @4
    wceq
    #
    wi
    #
    wph
    c2
    cz
    wcel
    cP
    cz
    wcel
    #
    @2
    2z
    wph
    cP
    cprime
    c2
    csn
    #
    cdif
    wcel
    #
    @9
    gausslemma2dlem0.p
    @11
    cP
    @11
    cP
    @11
    id
    gausslemma2dlem0a
    nnzd
    syl
    c2
    cP
    lgscl1
    sylancr
    @2
    @0
    @1
    wceq
    #
    @0
    cc0
    wceq
    #
    @0
    c1
    wceq
    #
    w3o
    wph
    @8
    wi
    #
    @0
    @1
    cc0
    c1
    c2
    cP
    clgs
    ovex
    eltp
    @12
    @15
    @13
    @14
    wph
    @8
    @12
    @1
    cP
    cmo
    co
    #
    @5
    wceq
    #
    @1
    @4
    wceq
    #
    wi
    #
    @4
    @1
    c1
    cpr
    wcel
    #
    wph
    @19
    wph
    cN
    cz
    wcel
    @20
    wph
    cN
    wph
    cP
    cH
    cM
    cN
    gausslemma2dlem0.p
    gausslemma2dlem0.m
    gausslemma2dlem0.h
    gausslemma2dlem0.n
    gausslemma2dlem0h
    nn0zd
    cN
    m1expcl2
    syl
    #
    @20
    @4
    @1
    wceq
    #
    @4
    c1
    wceq
    #
    wo
    #
    wph
    @19
    wi
    #
    @4
    @1
    c1
    @1
    cN
    cexp
    ovex
    elpr
    #
    @22
    @25
    @23
    @22
    @18
    wph
    @17
    @22
    @18
    @4
    @1
    eqcom
    biimpi
    2a1d
    wph
    @19
    @23
    @16
    c1
    cP
    cmo
    co
    #
    wceq
    #
    @1
    c1
    wceq
    #
    wi
    wph
    @28
    @16
    c1
    wceq
    #
    @29
    wph
    @27
    c1
    @16
    wph
    @11
    cP
    cr
    wcel
    #
    c1
    cP
    clt
    wbr
    #
    wa
    #
    @27
    c1
    wceq
    gausslemma2dlem0.p
    @11
    cP
    cprime
    wcel
    #
    @33
    cP
    cprime
    @10
    eldifi
    @34
    @31
    @32
    @34
    cP
    cP
    prmnn
    nnred
    cP
    prmgt1
    jca
    syl
    cP
    1mod
    3syl
    #
    eqeq2d
    wph
    @11
    cP
    c3
    cuz
    cfv
    wcel
    #
    @30
    @29
    wi
    #
    gausslemma2dlem0.p
    cP
    oddprmge3
    @36
    c1
    @16
    clt
    wbr
    #
    @37
    cP
    m1modge3gt1
    @30
    @38
    @29
    @30
    @38
    c1
    c1
    clt
    wbr
    #
    @29
    @16
    c1
    c1
    clt
    breq2
    @39
    @29
    c1
    1re
    ltnri
    pm2.21i
    syl6bi
    com12
    syl
    3syl
    #
    sylbid
    @23
    @17
    @28
    @18
    @29
    @23
    @5
    @27
    @16
    @4
    c1
    cP
    cmo
    oveq1
    #
    eqeq2d
    @4
    c1
    @1
    eqeq2
    imbi12d
    syl5ibr
    jaoi
    sylbi
    mpcom
    @12
    @6
    @17
    @7
    @18
    @12
    @3
    @16
    @5
    @0
    @1
    cP
    cmo
    oveq1
    eqeq1d
    @0
    @1
    @4
    eqeq1
    imbi12d
    syl5ibr
    wph
    @8
    @13
    cc0
    cP
    cmo
    co
    #
    @5
    wceq
    #
    cc0
    @4
    wceq
    #
    wi
    wph
    @43
    cc0
    @5
    wceq
    #
    @44
    wph
    @42
    cc0
    @5
    wph
    cP
    crp
    wcel
    #
    @42
    cc0
    wceq
    wph
    cP
    wph
    cP
    gausslemma2dlem0.p
    gausslemma2dlem0a
    nnrpd
    #
    cP
    0mod
    syl
    eqeq1d
    @20
    wph
    @45
    @44
    wi
    #
    @21
    @20
    @24
    wph
    @48
    wi
    #
    @26
    @22
    @49
    @23
    @22
    wph
    @48
    @22
    wph
    wa
    @45
    cc0
    @16
    wceq
    #
    @44
    @22
    @45
    @50
    wb
    wph
    @22
    @5
    @16
    cc0
    @4
    @1
    cP
    cmo
    oveq1
    #
    eqeq2d
    adantr
    wph
    @50
    @44
    wi
    @22
    wph
    @50
    @27
    cc0
    wceq
    #
    @44
    wph
    c1
    cr
    wcel
    #
    @46
    @52
    @50
    wb
    1re
    @47
    @53
    @46
    wa
    @52
    @16
    cc0
    wceq
    @50
    c1
    cP
    negmod0
    @16
    cc0
    eqcom
    syl6bb
    sylancr
    wph
    @52
    c1
    cc0
    wceq
    #
    @44
    wph
    @27
    c1
    cc0
    @35
    eqeq1d
    #
    @54
    c1
    cc0
    wne
    @44
    ax-1ne0
    @44
    c1
    cc0
    eqneqall
    mpi
    #
    syl6bi
    sylbird
    adantl
    sylbid
    ex
    @23
    wph
    @48
    @23
    wph
    wa
    @45
    cc0
    @27
    wceq
    #
    @44
    @23
    @45
    @57
    wb
    wph
    @23
    @5
    @27
    cc0
    @41
    eqeq2d
    adantr
    wph
    @57
    @44
    wi
    @23
    wph
    @57
    @54
    @44
    @57
    @52
    wph
    @54
    cc0
    @27
    eqcom
    @55
    syl5bb
    @56
    syl6bi
    adantl
    sylbid
    ex
    jaoi
    sylbi
    mpcom
    sylbid
    @13
    @6
    @43
    @7
    @44
    @13
    @3
    @42
    @5
    @0
    cc0
    cP
    cmo
    oveq1
    eqeq1d
    @0
    cc0
    @4
    eqeq1
    imbi12d
    syl5ibr
    wph
    @8
    @14
    @27
    @5
    wceq
    #
    c1
    @4
    wceq
    #
    wi
    wph
    @58
    c1
    @5
    wceq
    #
    @59
    wph
    @27
    c1
    @5
    @35
    eqeq1d
    @20
    wph
    @60
    @59
    wi
    #
    @21
    @20
    @24
    wph
    @61
    wi
    #
    @26
    @22
    @62
    @23
    wph
    @61
    @22
    c1
    @16
    wceq
    #
    c1
    @1
    wceq
    #
    wi
    wph
    @30
    @29
    @63
    @64
    @40
    c1
    @16
    eqcom
    c1
    @1
    eqcom
    3imtr4g
    @22
    @60
    @63
    @59
    @64
    @22
    @5
    @16
    c1
    @51
    eqeq2d
    @4
    @1
    c1
    eqeq2
    imbi12d
    syl5ibr
    @23
    @59
    wph
    @60
    @23
    @59
    @4
    c1
    eqcom
    biimpi
    2a1d
    jaoi
    sylbi
    mpcom
    sylbid
    @14
    @6
    @58
    @7
    @59
    @14
    @3
    @27
    @5
    @0
    c1
    cP
    cmo
    oveq1
    eqeq1d
    @0
    c1
    @4
    eqeq1
    imbi12d
    syl5ibr
    3jaoi
    sylbi
    mpcom
end
