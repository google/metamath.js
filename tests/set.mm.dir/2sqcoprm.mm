include "cc0.mm"
include "wne.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "2sqn0.mm"
include "wa.mm"
include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "gcdcld.mm"
include "adantr.mm"
include "wn.mm"
include "cn.mm"
include "cz.mm"
include "simpr.mm"
include "neneqd.mm"
include "intnanrd.mm"
include "gcdn0cl.mm"
include "syl21anc.mm"
include "nnsqcld.mm"
include "wi.mm"
include "cuz.mm"
include "cfv.mm"
include "cprime.mm"
include "nn0zd.mm"
include "sqnprm.mm"
include "syl.mm"
include "cdvds.mm"
include "wbr.mm"
include "caddc.mm"
include "zsqcl.mm"
include "gcddvds.mm"
include "syl2anc.mm"
include "simpld.mm"
include "dvdssqim.mm"
include "imp.mm"
include "simprd.mm"
include "w3a.mm"
include "dvds2add.mm"
include "syl32anc.mm"
include "breqtrd.mm"
include "wb.mm"
include "dvdsprm.mm"
include "mpbid.mm"
include "eqeltrd.mm"
include "mtand.mm"
include "eluz2b3.mm"
include "sylnib.mm"
include "imnan.mm"
include "sylibr.mm"
include "mpd.mm"
include "df-ne.mm"
include "notnotrd.mm"
include "nn0sqeq1.mm"
include "mpdan.mm"

theorem 2sqcoprm
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  assume 2sqcoprm.1: |- ( ph -> P e. Prime )
  assume 2sqcoprm.2: |- ( ph -> A e. ZZ )
  assume 2sqcoprm.3: |- ( ph -> B e. ZZ )
  assume 2sqcoprm.4: |- ( ph -> ( ( A ^ 2 ) + ( B ^ 2 ) ) = P )


  assert |- ( ph -> ( A gcd B ) = 1 )

  proof
    wph
    cA
    cc0
    wne
    #
    cA
    cB
    cgcd
    co
    #
    c1
    wceq
    #
    wph
    cA
    cB
    cP
    2sqcoprm.1
    2sqcoprm.2
    2sqcoprm.3
    2sqcoprm.4
    2sqn0
    wph
    @0
    wa
    #
    @1
    cn0
    wcel
    #
    @1
    c2
    cexp
    co
    #
    c1
    wceq
    #
    @2
    wph
    @4
    @0
    wph
    cA
    cB
    2sqcoprm.2
    2sqcoprm.3
    gcdcld
    #
    adantr
    @3
    @6
    @3
    @5
    c1
    wne
    #
    @6
    wn
    @3
    @5
    cn
    wcel
    #
    @8
    wn
    #
    @3
    @1
    @3
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cA
    cc0
    wceq
    #
    cB
    cc0
    wceq
    #
    wa
    wn
    @1
    cn
    wcel
    wph
    @11
    @0
    2sqcoprm.2
    adantr
    wph
    @12
    @0
    2sqcoprm.3
    adantr
    @3
    @13
    @14
    @3
    cA
    cc0
    wph
    @0
    simpr
    neneqd
    intnanrd
    cA
    cB
    gcdn0cl
    syl21anc
    nnsqcld
    wph
    @9
    @10
    wi
    #
    @0
    wph
    @9
    @8
    wa
    #
    wn
    @15
    wph
    @5
    c2
    cuz
    cfv
    wcel
    #
    @16
    wph
    @17
    @5
    cprime
    wcel
    #
    wph
    @1
    cz
    wcel
    #
    @18
    wn
    wph
    @1
    @7
    nn0zd
    #
    @1
    sqnprm
    syl
    wph
    @17
    wa
    #
    @5
    cP
    cprime
    @21
    @5
    cP
    cdvds
    wbr
    #
    @5
    cP
    wceq
    #
    wph
    @22
    @17
    wph
    @5
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    caddc
    co
    #
    cP
    cdvds
    wph
    @5
    cz
    wcel
    #
    @24
    cz
    wcel
    #
    @25
    cz
    wcel
    #
    @5
    @24
    cdvds
    wbr
    #
    @5
    @25
    cdvds
    wbr
    #
    @5
    @26
    cdvds
    wbr
    #
    wph
    @19
    @27
    @20
    @1
    zsqcl
    syl
    wph
    @11
    @28
    2sqcoprm.2
    cA
    zsqcl
    syl
    wph
    @12
    @29
    2sqcoprm.3
    cB
    zsqcl
    syl
    wph
    @19
    @11
    @1
    cA
    cdvds
    wbr
    #
    @30
    @20
    2sqcoprm.2
    wph
    @33
    @1
    cB
    cdvds
    wbr
    #
    wph
    @11
    @12
    @33
    @34
    wa
    2sqcoprm.2
    2sqcoprm.3
    cA
    cB
    gcddvds
    syl2anc
    #
    simpld
    @19
    @11
    wa
    @33
    @30
    @1
    cA
    dvdssqim
    imp
    syl21anc
    wph
    @19
    @12
    @34
    @31
    @20
    2sqcoprm.3
    wph
    @33
    @34
    @35
    simprd
    @19
    @12
    wa
    @34
    @31
    @1
    cB
    dvdssqim
    imp
    syl21anc
    @27
    @28
    @29
    w3a
    @30
    @31
    wa
    @32
    @5
    @24
    @25
    dvds2add
    imp
    syl32anc
    2sqcoprm.4
    breqtrd
    adantr
    @21
    @17
    cP
    cprime
    wcel
    #
    @22
    @23
    wb
    wph
    @17
    simpr
    wph
    @36
    @17
    2sqcoprm.1
    adantr
    #
    cP
    @5
    dvdsprm
    syl2anc
    mpbid
    @37
    eqeltrd
    mtand
    @5
    eluz2b3
    sylnib
    @9
    @8
    imnan
    sylibr
    adantr
    mpd
    @5
    c1
    df-ne
    sylnib
    notnotrd
    @1
    nn0sqeq1
    syl2anc
    mpdan
end
