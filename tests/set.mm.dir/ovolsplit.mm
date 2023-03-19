include "covol.mm"
include "cfv.mm"
include "cin.mm"
include "cdif.mm"
include "cun.mm"
include "cxad.mm"
include "co.mm"
include "cle.mm"
include "wceq.mm"
include "inundif.mm"
include "eqcomi.mm"
include "a1i.mm"
include "fveq2d.mm"
include "cpnf.mm"
include "wbr.mm"
include "wa.mm"
include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "wss.mm"
include "ssinss1d.mm"
include "ssdifssd.mm"
include "unssd.mm"
include "ovolcl.mm"
include "syl.mm"
include "pnfge.mm"
include "adantr.mm"
include "oveq1.mm"
include "adantl.mm"
include "cmnf.mm"
include "wne.mm"
include "cpw.mm"
include "cc0.mm"
include "cicc.mm"
include "cvv.mm"
include "wb.mm"
include "reex.mm"
include "ssexd.mm"
include "difexg.mm"
include "elpwg.mm"
include "mpbird.mm"
include "ovolf.mm"
include "ffvelrni.mm"
include "xrge0nemnfd.mm"
include "xaddpnf2.mm"
include "syl2anc.mm"
include "eqtr2d.mm"
include "breqtrd.mm"
include "wn.mm"
include "simpl.mm"
include "sselpwd.mm"
include "neqne.mm"
include "ge0xrre.mm"
include "oveq2.mm"
include "xaddpnf1.mm"
include "adantlr.mm"
include "simpll.mm"
include "simplr.mm"
include "w3a.mm"
include "caddc.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "ovolun.mm"
include "syl22anc.mm"
include "rexadd.mm"
include "eqcomd.mm"
include "3adant1.mm"
include "syl3anc.mm"
include "pm2.61dan.mm"
include "eqbrtrd.mm"

theorem ovolsplit
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  assume ovolsplit.1: |- ( ph -> A C_ RR )


  assert |- ( ph -> ( vol* ` A ) <_ ( ( vol* ` ( A i^i B ) ) +e ( vol* ` ( A \ B ) ) ) )

  proof
    wph
    cA
    covol
    cfv
    cA
    cB
    cin
    #
    cA
    cB
    cdif
    #
    cun
    #
    covol
    cfv
    #
    @0
    covol
    cfv
    #
    @1
    covol
    cfv
    #
    cxad
    co
    #
    cle
    wph
    cA
    @2
    covol
    cA
    @2
    wceq
    wph
    @2
    cA
    cA
    cB
    inundif
    eqcomi
    a1i
    fveq2d
    wph
    @4
    cpnf
    wceq
    #
    @3
    @6
    cle
    wbr
    #
    wph
    @7
    wa
    #
    @3
    cpnf
    @6
    cle
    wph
    @3
    cpnf
    cle
    wbr
    #
    @7
    wph
    @3
    cxr
    wcel
    #
    @10
    wph
    @2
    cr
    wss
    @11
    wph
    @0
    @1
    cr
    wph
    cA
    cB
    cr
    ovolsplit.1
    ssinss1d
    #
    wph
    cA
    cr
    cB
    ovolsplit.1
    ssdifssd
    #
    unssd
    @2
    ovolcl
    syl
    @3
    pnfge
    syl
    #
    adantr
    @9
    @6
    cpnf
    @5
    cxad
    co
    #
    cpnf
    @7
    @6
    @15
    wceq
    wph
    @4
    cpnf
    @5
    cxad
    oveq1
    adantl
    @9
    @5
    cxr
    wcel
    #
    @5
    cmnf
    wne
    #
    @15
    cpnf
    wceq
    wph
    @16
    @7
    wph
    @1
    cr
    wss
    #
    @16
    @13
    @1
    ovolcl
    syl
    adantr
    wph
    @17
    @7
    wph
    @5
    wph
    @1
    cr
    cpw
    #
    wcel
    #
    @5
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    wph
    @20
    @18
    @13
    wph
    @1
    cvv
    wcel
    #
    @20
    @18
    wb
    wph
    cA
    cvv
    wcel
    @23
    wph
    cA
    cr
    cvv
    cr
    cvv
    wcel
    wph
    reex
    a1i
    #
    ovolsplit.1
    ssexd
    cA
    cB
    cvv
    difexg
    syl
    @1
    cr
    cvv
    elpwg
    syl
    mpbird
    @19
    @21
    @1
    covol
    ovolf
    ffvelrni
    syl
    #
    xrge0nemnfd
    adantr
    @5
    xaddpnf2
    syl2anc
    eqtr2d
    breqtrd
    wph
    @7
    wn
    #
    wa
    #
    wph
    @4
    cr
    wcel
    #
    @8
    wph
    @26
    simpl
    @27
    @4
    @21
    wcel
    #
    @4
    cpnf
    wne
    #
    @28
    wph
    @29
    @26
    wph
    @0
    @19
    wcel
    @29
    wph
    @0
    cr
    cvv
    @24
    @12
    sselpwd
    @19
    @21
    @0
    covol
    ovolf
    ffvelrni
    syl
    #
    adantr
    @26
    @30
    wph
    @4
    cpnf
    neqne
    adantl
    @4
    ge0xrre
    syl2anc
    wph
    @28
    wa
    #
    @5
    cpnf
    wceq
    #
    @8
    wph
    @33
    @8
    @28
    wph
    @33
    wa
    #
    @3
    cpnf
    @6
    cle
    wph
    @10
    @33
    @14
    adantr
    @34
    @6
    @4
    cpnf
    cxad
    co
    #
    cpnf
    @33
    @6
    @35
    wceq
    wph
    @5
    cpnf
    @4
    cxad
    oveq2
    adantl
    wph
    @35
    cpnf
    wceq
    #
    @33
    wph
    @4
    cxr
    wcel
    #
    @4
    cmnf
    wne
    @36
    wph
    @0
    cr
    wss
    #
    @37
    @12
    @0
    ovolcl
    syl
    wph
    @4
    @31
    xrge0nemnfd
    @4
    xaddpnf1
    syl2anc
    adantr
    eqtr2d
    breqtrd
    adantlr
    @32
    @33
    wn
    #
    wa
    wph
    @28
    @5
    cr
    wcel
    #
    @8
    wph
    @28
    @39
    simpll
    wph
    @28
    @39
    simplr
    wph
    @39
    @40
    @28
    wph
    @39
    wa
    @22
    @5
    cpnf
    wne
    #
    @40
    wph
    @22
    @39
    @25
    adantr
    @39
    @41
    wph
    @5
    cpnf
    neqne
    adantl
    @5
    ge0xrre
    syl2anc
    adantlr
    wph
    @28
    @40
    w3a
    #
    @3
    @4
    @5
    caddc
    co
    #
    @6
    cle
    @42
    @38
    @28
    @18
    @40
    @3
    @43
    cle
    wbr
    wph
    @28
    @38
    @40
    @12
    3ad2ant1
    wph
    @28
    @40
    simp2
    wph
    @28
    @18
    @40
    @13
    3ad2ant1
    wph
    @28
    @40
    simp3
    @0
    @1
    ovolun
    syl22anc
    @28
    @40
    @43
    @6
    wceq
    wph
    @28
    @40
    wa
    @6
    @43
    @4
    @5
    rexadd
    eqcomd
    3adant1
    breqtrd
    syl3anc
    pm2.61dan
    syl2anc
    pm2.61dan
    eqbrtrd
end
