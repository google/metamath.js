include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "caddc.mm"
include "cmul.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmo.mm"
include "cc0.mm"
include "wceq.mm"
include "cz.mm"
include "wcel.mm"
include "adantr.mm"
include "cneg.mm"
include "cn.mm"
include "nnred.mm"
include "rehalfcld.mm"
include "recnd.mm"
include "negnegd.mm"
include "wn.mm"
include "4sqlem5.mm"
include "simpld.mm"
include "zred.mm"
include "cle.mm"
include "clt.mm"
include "4sqlem6.mm"
include "simprd.mm"
include "ltned.mm"
include "neneqd.mm"
include "wo.mm"
include "2cnd.mm"
include "sqvald.mm"
include "oveq2d.mm"
include "nncnd.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "sqdivd.mm"
include "sqcld.mm"
include "divdiv1d.mm"
include "3eqtr4d.mm"
include "halfcld.mm"
include "zcnd.mm"
include "subeq0d.mm"
include "eqtr2d.mm"
include "cc.mm"
include "wb.mm"
include "sqeqor.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "ord.mm"
include "mpd.mm"
include "eqeltrrd.mm"
include "znegcld.mm"
include "zaddcld.mm"
include "nnrpd.mm"
include "modcld.mm"
include "0cnd.mm"
include "df-neg.mm"
include "3eqtr3g.mm"
include "subcan2d.mm"
include "dvdsval3.mm"
include "mpbird.mm"
include "nnzd.mm"
include "dvdssq.mm"
include "nnne0d.mm"
include "dvdsmulcr.mm"
include "syl112anc.mm"
include "eqbrtrd.mm"
include "wi.mm"
include "zsqcl.mm"
include "syl.mm"
include "zmulcld.mm"
include "dvds2sub.mm"
include "syl3anc.mm"
include "mp2and.mm"
include "oveq1d.mm"
include "subdid.mm"
include "2halvesd.mm"
include "pnpcan2d.mm"
include "eqtr3d.mm"
include "subsq.mm"
include "3eqtr2d.mm"
include "breqtrd.mm"

theorem 4sqlem10
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cM: class M
  assume 4sqlem5.2: |- ( ph -> A e. ZZ )
  assume 4sqlem5.3: |- ( ph -> M e. NN )
  assume 4sqlem5.4: |- B = ( ( ( A + ( M / 2 ) ) mod M ) - ( M / 2 ) )
  assume 4sqlem10.5: |- ( ( ph /\ ps ) -> ( ( ( ( M ^ 2 ) / 2 ) / 2 ) - ( B ^ 2 ) ) = 0 )


  assert |- ( ( ph /\ ps ) -> ( M ^ 2 ) || ( ( A ^ 2 ) - ( ( ( M ^ 2 ) / 2 ) / 2 ) ) )

  proof
    wph
    wps
    wa
    #
    cM
    c2
    cexp
    co
    #
    cA
    cM
    c2
    cdiv
    co
    #
    caddc
    co
    #
    c2
    cexp
    co
    #
    @3
    cM
    cmul
    co
    #
    cmin
    co
    #
    cA
    c2
    cexp
    co
    #
    @1
    c2
    cdiv
    co
    #
    c2
    cdiv
    co
    #
    cmin
    co
    #
    cdvds
    @0
    @1
    @4
    cdvds
    wbr
    #
    @1
    @5
    cdvds
    wbr
    #
    @1
    @6
    cdvds
    wbr
    #
    @0
    cM
    @3
    cdvds
    wbr
    #
    @11
    @0
    @14
    @3
    cM
    cmo
    co
    #
    cc0
    wceq
    #
    @0
    @15
    cc0
    @2
    @0
    @15
    @0
    @3
    cM
    @0
    @3
    @0
    cA
    @2
    wph
    cA
    cz
    wcel
    wps
    4sqlem5.2
    adantr
    #
    @0
    @2
    cneg
    #
    cneg
    @2
    cz
    @0
    @2
    @0
    @2
    @0
    cM
    @0
    cM
    wph
    cM
    cn
    wcel
    #
    wps
    4sqlem5.3
    adantr
    #
    nnred
    rehalfcld
    recnd
    #
    negnegd
    @0
    @18
    @0
    cB
    @18
    cz
    @0
    cB
    @2
    wceq
    #
    wn
    cB
    @18
    wceq
    #
    @0
    cB
    @2
    @0
    cB
    @2
    @0
    cB
    @0
    cB
    cz
    wcel
    #
    cA
    cB
    cmin
    co
    cM
    cdiv
    co
    cz
    wcel
    #
    wph
    @24
    @25
    wa
    wps
    wph
    cA
    cB
    cM
    4sqlem5.2
    4sqlem5.3
    4sqlem5.4
    4sqlem5
    adantr
    simpld
    #
    zred
    @0
    @18
    cB
    cle
    wbr
    #
    cB
    @2
    clt
    wbr
    #
    wph
    @27
    @28
    wa
    wps
    wph
    cA
    cB
    cM
    4sqlem5.2
    4sqlem5.3
    4sqlem5.4
    4sqlem6
    adantr
    simprd
    ltned
    neneqd
    @0
    @22
    @23
    @0
    cB
    c2
    cexp
    co
    #
    @2
    c2
    cexp
    co
    #
    wceq
    #
    @22
    @23
    wo
    #
    @0
    @30
    @9
    @29
    @0
    @1
    c2
    c2
    cexp
    co
    #
    cdiv
    co
    @1
    c2
    c2
    cmul
    co
    #
    cdiv
    co
    @30
    @9
    @0
    @33
    @34
    @1
    cdiv
    @0
    c2
    @0
    2cnd
    #
    sqvald
    oveq2d
    @0
    cM
    c2
    @0
    cM
    @20
    nncnd
    #
    @35
    c2
    cc0
    wne
    @0
    2ne0
    a1i
    #
    sqdivd
    @0
    @1
    c2
    c2
    @0
    cM
    @36
    sqcld
    #
    @35
    @35
    @37
    @37
    divdiv1d
    3eqtr4d
    #
    @0
    @9
    @29
    @0
    @8
    @0
    @1
    @38
    halfcld
    halfcld
    @0
    cB
    @0
    cB
    @26
    zcnd
    #
    sqcld
    4sqlem10.5
    subeq0d
    eqtr2d
    @0
    cB
    cc
    wcel
    @2
    cc
    wcel
    #
    @31
    @32
    wb
    @40
    @21
    cB
    @2
    sqeqor
    syl2anc
    mpbid
    ord
    mpd
    #
    @26
    eqeltrrd
    znegcld
    eqeltrrd
    zaddcld
    #
    zred
    @0
    cM
    @20
    nnrpd
    modcld
    recnd
    @0
    0cnd
    @21
    @0
    cB
    @18
    @15
    @2
    cmin
    co
    cc0
    @2
    cmin
    co
    @42
    4sqlem5.4
    @2
    df-neg
    3eqtr3g
    subcan2d
    @0
    @19
    @3
    cz
    wcel
    #
    @14
    @16
    wb
    @20
    @43
    cM
    @3
    dvdsval3
    syl2anc
    mpbird
    #
    @0
    cM
    cz
    wcel
    #
    @44
    @14
    @11
    wb
    @0
    cM
    @20
    nnzd
    #
    @43
    cM
    @3
    dvdssq
    syl2anc
    mpbid
    @0
    @1
    cM
    cM
    cmul
    co
    #
    @5
    cdvds
    @0
    cM
    @36
    sqvald
    @0
    @48
    @5
    cdvds
    wbr
    #
    @14
    @45
    @0
    @46
    @44
    @46
    cM
    cc0
    wne
    @49
    @14
    wb
    @47
    @43
    @47
    @0
    cM
    @20
    nnne0d
    cM
    cM
    @3
    dvdsmulcr
    syl112anc
    mpbird
    eqbrtrd
    @0
    @1
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    @5
    cz
    wcel
    @11
    @12
    wa
    @13
    wi
    @0
    @46
    @50
    @47
    cM
    zsqcl
    syl
    @0
    @44
    @51
    @43
    @3
    zsqcl
    syl
    @0
    @3
    cM
    @43
    @47
    zmulcld
    @1
    @4
    @5
    dvds2sub
    syl3anc
    mp2and
    @0
    @6
    @3
    @3
    cmul
    co
    #
    @5
    cmin
    co
    @3
    @3
    cM
    cmin
    co
    #
    cmul
    co
    #
    @10
    @0
    @4
    @52
    @5
    cmin
    @0
    @3
    @0
    @3
    @43
    zcnd
    #
    sqvald
    oveq1d
    @0
    @3
    @3
    cM
    @55
    @55
    @36
    subdid
    @0
    @54
    @3
    cA
    @2
    cmin
    co
    #
    cmul
    co
    #
    @7
    @30
    cmin
    co
    #
    @10
    @0
    @53
    @56
    @3
    cmul
    @0
    @3
    @2
    @2
    caddc
    co
    #
    cmin
    co
    @53
    @56
    @0
    @59
    cM
    @3
    cmin
    @0
    cM
    @36
    2halvesd
    oveq2d
    @0
    cA
    @2
    @2
    @0
    cA
    @17
    zcnd
    #
    @21
    @21
    pnpcan2d
    eqtr3d
    oveq2d
    @0
    cA
    cc
    wcel
    @41
    @58
    @57
    wceq
    @60
    @21
    cA
    @2
    subsq
    syl2anc
    @0
    @30
    @9
    @7
    cmin
    @39
    oveq2d
    3eqtr2d
    3eqtr2d
    breqtrd
end
