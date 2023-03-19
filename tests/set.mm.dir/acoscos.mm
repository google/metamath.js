include "cc.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "cc0.mm"
include "cpi.mm"
include "cioo.mm"
include "co.mm"
include "wa.mm"
include "ccos.mm"
include "cacos.mm"
include "c2.mm"
include "cdiv.mm"
include "casin.mm"
include "cmin.mm"
include "wceq.mm"
include "coscl.mm"
include "adantr.mm"
include "acosval.mm"
include "syl.mm"
include "csin.mm"
include "picn.mm"
include "halfcl.mm"
include "ax-mp.mm"
include "simpl.mm"
include "nncan.mm"
include "sylancr.mm"
include "fveq2d.mm"
include "subcl.mm"
include "coshalfpim.mm"
include "eqtr3d.mm"
include "cneg.mm"
include "halfpire.mm"
include "recni.mm"
include "resub.mm"
include "cr.mm"
include "rere.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "clt.mm"
include "wbr.mm"
include "recl.mm"
include "resubcl.mm"
include "a1i.mm"
include "neghalfpire.mm"
include "eliooord.mm"
include "adantl.mm"
include "simprd.mm"
include "caddc.mm"
include "subnegi.mm"
include "pidiv2halves.mm"
include "eqtri.mm"
include "syl6breqr.mm"
include "ltsub13d.mm"
include "simpld.mm"
include "wb.mm"
include "ltsubpos.mm"
include "sylancl.mm"
include "mpbid.mm"
include "cxr.mm"
include "w3a.mm"
include "rexri.mm"
include "elioo2.mm"
include "mp2an.mm"
include "syl3anbrc.mm"
include "eqeltrd.mm"
include "asinsin.mm"
include "syl2anc.mm"
include "eqtr2d.mm"
include "asincl.mm"
include "subsub23.mm"
include "syl3anc.mm"
include "eqtrd.mm"

theorem acoscos
  let cA: class A


  assert |- ( ( A e. CC /\ ( Re ` A ) e. ( 0 (,) _pi ) ) -> ( arccos ` ( cos ` A ) ) = A )

  proof
    cA
    cc
    wcel
    #
    cA
    cre
    cfv
    #
    cc0
    cpi
    cioo
    co
    wcel
    #
    wa
    #
    cA
    ccos
    cfv
    #
    cacos
    cfv
    #
    cpi
    c2
    cdiv
    co
    #
    @4
    casin
    cfv
    #
    cmin
    co
    #
    cA
    @3
    @4
    cc
    wcel
    #
    @5
    @8
    wceq
    @0
    @9
    @2
    cA
    coscl
    adantr
    #
    @4
    acosval
    syl
    @3
    @6
    cA
    cmin
    co
    #
    @7
    wceq
    #
    @8
    cA
    wceq
    #
    @3
    @7
    @11
    csin
    cfv
    #
    casin
    cfv
    #
    @11
    @3
    @4
    @14
    casin
    @3
    @6
    @11
    cmin
    co
    #
    ccos
    cfv
    #
    @4
    @14
    @3
    @16
    cA
    ccos
    @3
    @6
    cc
    wcel
    #
    @0
    @16
    cA
    wceq
    cpi
    cc
    wcel
    @18
    picn
    cpi
    halfcl
    ax-mp
    #
    @0
    @2
    simpl
    #
    @6
    cA
    nncan
    sylancr
    fveq2d
    @3
    @11
    cc
    wcel
    #
    @17
    @14
    wceq
    @3
    @18
    @0
    @21
    @19
    @20
    @6
    cA
    subcl
    sylancr
    #
    @11
    coshalfpim
    syl
    eqtr3d
    fveq2d
    @3
    @21
    @11
    cre
    cfv
    #
    @6
    cneg
    #
    @6
    cioo
    co
    #
    wcel
    @15
    @11
    wceq
    @22
    @3
    @23
    @6
    @1
    cmin
    co
    #
    @25
    @3
    @23
    @6
    cre
    cfv
    #
    @1
    cmin
    co
    #
    @26
    @3
    @18
    @0
    @23
    @28
    wceq
    @6
    halfpire
    recni
    #
    @20
    @6
    cA
    resub
    sylancr
    @27
    @6
    @1
    cmin
    @6
    cr
    wcel
    #
    @27
    @6
    wceq
    halfpire
    @6
    rere
    ax-mp
    oveq1i
    syl6eq
    @3
    @26
    cr
    wcel
    #
    @24
    @26
    clt
    wbr
    #
    @26
    @6
    clt
    wbr
    #
    @26
    @25
    wcel
    #
    @3
    @30
    @1
    cr
    wcel
    #
    @31
    halfpire
    @0
    @35
    @2
    cA
    recl
    adantr
    #
    @6
    @1
    resubcl
    sylancr
    @3
    @1
    @6
    @24
    @36
    @30
    @3
    halfpire
    a1i
    @24
    cr
    wcel
    @3
    neghalfpire
    a1i
    @3
    @1
    cpi
    @6
    @24
    cmin
    co
    #
    clt
    @3
    cc0
    @1
    clt
    wbr
    #
    @1
    cpi
    clt
    wbr
    #
    @2
    @38
    @39
    wa
    @0
    @1
    cc0
    cpi
    eliooord
    adantl
    #
    simprd
    @37
    @6
    @6
    caddc
    co
    cpi
    @6
    @6
    @29
    @29
    subnegi
    pidiv2halves
    eqtri
    syl6breqr
    ltsub13d
    @3
    @38
    @33
    @3
    @38
    @39
    @40
    simpld
    @3
    @35
    @30
    @38
    @33
    wb
    @36
    halfpire
    @1
    @6
    ltsubpos
    sylancl
    mpbid
    @24
    cxr
    wcel
    @6
    cxr
    wcel
    @34
    @31
    @32
    @33
    w3a
    wb
    @24
    neghalfpire
    rexri
    @6
    halfpire
    rexri
    @24
    @6
    @26
    elioo2
    mp2an
    syl3anbrc
    eqeltrd
    @11
    asinsin
    syl2anc
    eqtr2d
    @3
    @18
    @0
    @7
    cc
    wcel
    #
    @12
    @13
    wb
    @18
    @3
    @29
    a1i
    @20
    @3
    @9
    @41
    @10
    @4
    asincl
    syl
    @6
    cA
    @7
    subsub23
    syl3anc
    mpbid
    eqtrd
end
