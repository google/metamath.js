include "cpi.mm"
include "cneg.mm"
include "cioc.mm"
include "co.mm"
include "wcel.mm"
include "ccos.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "c2.mm"
include "cdiv.mm"
include "cpr.mm"
include "wa.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "w3a.mm"
include "simpl.mm"
include "cxr.mm"
include "wb.mm"
include "pire.mm"
include "renegcli.mm"
include "rexri.mm"
include "elioc2.mm"
include "mp2an.mm"
include "sylib.mm"
include "simp1d.mm"
include "0re.mm"
include "a1i.mm"
include "adantr.mm"
include "recnd.mm"
include "cc.mm"
include "cosneg.mm"
include "syl.mm"
include "simplr.mm"
include "eqtrd.mm"
include "cicc.mm"
include "renegcld.mm"
include "simpr.mm"
include "le0neg1d.mm"
include "mpbid.mm"
include "simp2d.mm"
include "ltnegcon1d.mm"
include "ltled.mm"
include "elicc2i.mm"
include "syl3anbrc.mm"
include "coseq00topi.mm"
include "negcon1ad.mm"
include "eqcomd.mm"
include "wi.mm"
include "halfpire.mm"
include "prid2g.mm"
include "eleq1a.mm"
include "mp2b.mm"
include "simp3d.mm"
include "prid1g.mm"
include "lecasei.mm"
include "wo.mm"
include "elpri.mm"
include "fveq2.mm"
include "coshalfpi.mm"
include "syl6eq.mm"
include "cosneghalfpi.mm"
include "jaoi.mm"
include "adantl.mm"
include "impbida.mm"

theorem coseq0negpitopi
  let cA: class A


  assert |- ( A e. ( -u _pi (,] _pi ) -> ( ( cos ` A ) = 0 <-> A e. { ( _pi / 2 ) , -u ( _pi / 2 ) } ) )

  proof
    cA
    cpi
    cneg
    #
    cpi
    cioc
    co
    wcel
    #
    cA
    ccos
    cfv
    #
    cc0
    wceq
    #
    cA
    cpi
    c2
    cdiv
    co
    #
    @4
    cneg
    #
    cpr
    #
    wcel
    #
    @1
    @3
    wa
    #
    @7
    cA
    cc0
    @8
    cA
    cr
    wcel
    #
    @0
    cA
    clt
    wbr
    #
    cA
    cpi
    cle
    wbr
    #
    @8
    @1
    @9
    @10
    @11
    w3a
    #
    @1
    @3
    simpl
    @0
    cxr
    wcel
    cpi
    cr
    wcel
    #
    @1
    @12
    wb
    @0
    cpi
    pire
    renegcli
    rexri
    pire
    @0
    cpi
    cA
    elioc2
    mp2an
    sylib
    #
    simp1d
    #
    cc0
    cr
    wcel
    @8
    0re
    a1i
    @8
    cA
    cc0
    cle
    wbr
    #
    wa
    #
    cA
    @5
    wceq
    #
    @7
    @17
    @5
    cA
    @17
    cA
    @4
    @17
    cA
    @8
    @9
    @16
    @15
    adantr
    #
    recnd
    @17
    cA
    cneg
    #
    ccos
    cfv
    #
    cc0
    wceq
    #
    @20
    @4
    wceq
    #
    @17
    @21
    @2
    cc0
    @17
    cA
    cc
    wcel
    #
    @21
    @2
    wceq
    @8
    @24
    @16
    @8
    cA
    @15
    recnd
    adantr
    cA
    cosneg
    syl
    @1
    @3
    @16
    simplr
    eqtrd
    @17
    @20
    cc0
    cpi
    cicc
    co
    #
    wcel
    #
    @22
    @23
    wb
    @17
    @20
    cr
    wcel
    #
    cc0
    @20
    cle
    wbr
    #
    @20
    cpi
    cle
    wbr
    #
    @26
    @8
    @27
    @16
    @8
    cA
    @15
    renegcld
    #
    adantr
    @17
    @16
    @28
    @8
    @16
    simpr
    @17
    cA
    @19
    le0neg1d
    mpbid
    @8
    @29
    @16
    @8
    @20
    cpi
    @30
    @13
    @8
    pire
    a1i
    #
    @8
    cpi
    cA
    @31
    @15
    @8
    @9
    @10
    @11
    @14
    simp2d
    ltnegcon1d
    ltled
    adantr
    cc0
    cpi
    @20
    0re
    pire
    elicc2i
    syl3anbrc
    @20
    coseq00topi
    syl
    mpbid
    negcon1ad
    eqcomd
    @5
    cr
    wcel
    @5
    @6
    wcel
    @18
    @7
    wi
    @4
    halfpire
    renegcli
    @4
    @5
    cr
    prid2g
    @5
    @6
    cA
    eleq1a
    mp2b
    syl
    @8
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cA
    @4
    wceq
    #
    @7
    @33
    @3
    @34
    @1
    @3
    @32
    simplr
    @33
    cA
    @25
    wcel
    #
    @3
    @34
    wb
    @33
    @9
    @32
    @11
    @35
    @8
    @9
    @32
    @15
    adantr
    @8
    @32
    simpr
    @8
    @11
    @32
    @8
    @9
    @10
    @11
    @14
    simp3d
    adantr
    cc0
    cpi
    cA
    0re
    pire
    elicc2i
    syl3anbrc
    cA
    coseq00topi
    syl
    mpbid
    @4
    cr
    wcel
    @4
    @6
    wcel
    @34
    @7
    wi
    halfpire
    @4
    @5
    cr
    prid1g
    @4
    @6
    cA
    eleq1a
    mp2b
    syl
    lecasei
    @7
    @3
    @1
    @7
    @34
    @18
    wo
    @3
    cA
    @4
    @5
    elpri
    @34
    @3
    @18
    @34
    @2
    @4
    ccos
    cfv
    cc0
    cA
    @4
    ccos
    fveq2
    coshalfpi
    syl6eq
    @18
    @2
    @5
    ccos
    cfv
    cc0
    cA
    @5
    ccos
    fveq2
    cosneghalfpi
    syl6eq
    jaoi
    syl
    adantl
    impbida
end
