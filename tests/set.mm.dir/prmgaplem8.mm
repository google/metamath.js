include "cv.mm"
include "cfv.mm"
include "c2.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cprime.mm"
include "wnel.mm"
include "c1.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "cmin.mm"
include "cle.mm"
include "wa.mm"
include "wcel.mm"
include "wi.mm"
include "cr.mm"
include "prmnn.mm"
include "nnred.mm"
include "ad2antll.mm"
include "ad2antlr.mm"
include "adantl.mm"
include "ad2antrr.mm"
include "cn.mm"
include "cmap.mm"
include "wf.mm"
include "elmapi.mm"
include "ffvelrn.mm"
include "ex.mm"
include "3syl.mm"
include "mpd.mm"
include "1red.mm"
include "readdcld.mm"
include "wceq.mm"
include "nncnd.mm"
include "1cnd.mm"
include "add32d.mm"
include "adantr.mm"
include "cz.mm"
include "wb.mm"
include "nnzd.mm"
include "zaddcld.mm"
include "prmz.mm"
include "zltp1le.mm"
include "syl2an.mm"
include "biimpa.mm"
include "eqbrtrd.mm"
include "expcom.mm"
include "imp.mm"
include "df-2.mm"
include "a1i.mm"
include "oveq2d.mm"
include "addassd.mm"
include "eqtr4d.mm"
include "breq2d.mm"
include "peano2zd.mm"
include "zleltp1.mm"
include "syl2anr.mm"
include "biimprd.mm"
include "sylbid.mm"
include "com12.mm"
include "lesub3d.mm"
include "3adant3.mm"
include "impcom.mm"
include "simpr3.mm"
include "jca.mm"
include "prmgaplem7.mm"
include "reximddv2.mm"

theorem prmgaplem8
  let wph: wff ph
  let vz: setvar z
  let vi: setvar i
  let cF: class F
  let cN: class N
  let vq: setvar q
  let vp: setvar p
  let vr: setvar r
  let vs: setvar s
  let vj: setvar j
  assume prmgaplem7.n: |- ( ph -> N e. NN )
  assume prmgaplem7.f: |- ( ph -> F e. ( NN ^m NN ) )
  assume prmgaplem7.i: |- ( ph -> A. i e. ( 2 ... N ) 1 < ( ( ( F ` N ) + i ) gcd i ) )

  disjoint F p
  disjoint F q
  disjoint F z
  disjoint p q
  disjoint p z
  disjoint q z
  disjoint F i
  disjoint N p
  disjoint N q
  disjoint N z
  disjoint N i
  disjoint p ph
  disjoint ph q
  disjoint ph z
  disjoint F r
  disjoint F s
  disjoint p r
  disjoint p s
  disjoint q r
  disjoint q s
  disjoint r s
  disjoint r z
  disjoint s z
  disjoint F j
  disjoint i j
  disjoint N r
  disjoint N s
  disjoint N j
  disjoint j ph
  disjoint j p
  disjoint j q
  disjoint j z
  assert |- ( ph -> E. p e. Prime E. q e. Prime ( N <_ ( q - p ) /\ A. z e. ( ( p + 1 ) ..^ q ) z e/ Prime ) )

  proof
    wph
    vp
    cv
    #
    cN
    cF
    cfv
    #
    c2
    caddc
    co
    #
    clt
    wbr
    #
    @1
    cN
    caddc
    co
    #
    vq
    cv
    #
    clt
    wbr
    #
    vz
    cv
    cprime
    wnel
    vz
    @0
    c1
    caddc
    co
    @5
    cfzo
    co
    wral
    #
    w3a
    #
    cN
    @5
    @0
    cmin
    co
    cle
    wbr
    #
    @7
    wa
    vp
    vq
    cprime
    cprime
    wph
    @0
    cprime
    wcel
    #
    wa
    #
    @5
    cprime
    wcel
    #
    wa
    #
    @8
    wa
    @9
    @7
    @8
    @13
    @9
    @3
    @6
    @13
    @9
    wi
    @7
    @3
    @6
    wa
    #
    @13
    @9
    @14
    @13
    wa
    #
    @5
    @0
    cN
    @1
    c1
    caddc
    co
    #
    @12
    @5
    cr
    wcel
    @14
    @11
    @12
    @5
    @5
    prmnn
    nnred
    ad2antll
    @13
    @0
    cr
    wcel
    #
    @14
    @10
    @17
    wph
    @12
    @10
    @0
    @0
    prmnn
    nnred
    ad2antlr
    adantl
    @13
    cN
    cr
    wcel
    #
    @14
    wph
    @18
    @10
    @12
    wph
    cN
    prmgaplem7.n
    nnred
    ad2antrr
    adantl
    @15
    @1
    c1
    @13
    @1
    cr
    wcel
    #
    @14
    wph
    @19
    @10
    @12
    wph
    @1
    wph
    cN
    cn
    wcel
    #
    @1
    cn
    wcel
    #
    prmgaplem7.n
    wph
    cF
    cn
    cn
    cmap
    co
    wcel
    cn
    cn
    cF
    wf
    #
    @20
    @21
    wi
    prmgaplem7.f
    cF
    cn
    cn
    elmapi
    @22
    @20
    @21
    cn
    cn
    cN
    cF
    ffvelrn
    ex
    3syl
    mpd
    #
    nnred
    ad2antrr
    adantl
    @15
    1red
    readdcld
    @14
    @13
    @16
    cN
    caddc
    co
    #
    @5
    cle
    wbr
    #
    @6
    @13
    @25
    wi
    @3
    @13
    @6
    @25
    @13
    @6
    wa
    @24
    @4
    c1
    caddc
    co
    #
    @5
    cle
    @11
    @24
    @26
    wceq
    #
    @12
    @6
    wph
    @27
    @10
    wph
    @1
    c1
    cN
    wph
    @1
    @23
    nncnd
    #
    wph
    1cnd
    #
    wph
    cN
    prmgaplem7.n
    nncnd
    add32d
    adantr
    ad2antrr
    @13
    @6
    @26
    @5
    cle
    wbr
    #
    @11
    @4
    cz
    wcel
    @5
    cz
    wcel
    @6
    @30
    wb
    @12
    @11
    @1
    cN
    wph
    @1
    cz
    wcel
    @10
    wph
    @1
    @23
    nnzd
    #
    adantr
    wph
    cN
    cz
    wcel
    @10
    wph
    cN
    prmgaplem7.n
    nnzd
    adantr
    zaddcld
    @5
    prmz
    @4
    @5
    zltp1le
    syl2an
    biimpa
    eqbrtrd
    expcom
    adantl
    imp
    @14
    @13
    @0
    @16
    cle
    wbr
    #
    @3
    @13
    @32
    wi
    @6
    @13
    @3
    @32
    @11
    @3
    @32
    wi
    @12
    @11
    @3
    @0
    @16
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @32
    @11
    @2
    @33
    @0
    clt
    wph
    @2
    @33
    wceq
    @10
    wph
    @2
    @1
    c1
    c1
    caddc
    co
    #
    caddc
    co
    @33
    wph
    c2
    @35
    @1
    caddc
    c2
    @35
    wceq
    wph
    df-2
    a1i
    oveq2d
    wph
    @1
    c1
    c1
    @28
    @29
    @29
    addassd
    eqtr4d
    adantr
    breq2d
    @11
    @32
    @34
    @10
    @0
    cz
    wcel
    @16
    cz
    wcel
    @32
    @34
    wb
    wph
    @0
    prmz
    wph
    @1
    @31
    peano2zd
    @0
    @16
    zleltp1
    syl2anr
    biimprd
    sylbid
    adantr
    com12
    adantr
    imp
    lesub3d
    ex
    3adant3
    impcom
    @13
    @3
    @6
    @7
    simpr3
    jca
    wph
    vz
    vi
    cF
    cN
    vq
    vp
    prmgaplem7.n
    prmgaplem7.f
    prmgaplem7.i
    prmgaplem7
    reximddv2
end
