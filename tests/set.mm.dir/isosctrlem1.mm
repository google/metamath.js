include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wn.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "clog.mm"
include "cim.mm"
include "cpi.mm"
include "cr.mm"
include "wa.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "mpan.mm"
include "adantr.mm"
include "cc0.mm"
include "wb.mm"
include "subeq0.mm"
include "notbid.mm"
include "biimpar.mm"
include "neqned.mm"
include "logcld.mm"
include "imcld.mm"
include "3adant2.mm"
include "c2.mm"
include "cdiv.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wne.mm"
include "cre.mm"
include "3ad2ant1.mm"
include "releabs.mm"
include "breq2.mm"
include "adantl.mm"
include "mpbid.mm"
include "recl.mm"
include "recnd.mm"
include "subidd.mm"
include "simpl.mm"
include "recld.mm"
include "1red.mm"
include "simpr.mm"
include "lesub1dd.mm"
include "eqbrtrrd.mm"
include "syldan.mm"
include "resub.mm"
include "re1.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "breqtrrd.mm"
include "3adant3.mm"
include "cneg.mm"
include "cicc.mm"
include "argrege0.mm"
include "cxr.mm"
include "neghalfpirx.mm"
include "halfpire.mm"
include "rexri.mm"
include "iccleub.mm"
include "mp3an12.mm"
include "syl.mm"
include "syl3anc.mm"
include "crp.mm"
include "pirp.mm"
include "rphalflt.mm"
include "ax-mp.mm"
include "jctir.mm"
include "wi.mm"
include "pire.mm"
include "a1i.mm"
include "rehalfcld.mm"
include "lelttr.mm"
include "mpd.mm"
include "ltned.mm"

theorem isosctrlem1
  let cA: class A


  assert |- ( ( A e. CC /\ ( abs ` A ) = 1 /\ -. 1 = A ) -> ( Im ` ( log ` ( 1 - A ) ) ) =/= _pi )

  proof
    cA
    cc
    wcel
    #
    cA
    cabs
    cfv
    #
    c1
    wceq
    #
    c1
    cA
    wceq
    #
    wn
    #
    w3a
    #
    c1
    cA
    cmin
    co
    #
    clog
    cfv
    #
    cim
    cfv
    #
    cpi
    @0
    @4
    @8
    cr
    wcel
    #
    @2
    @0
    @4
    wa
    #
    @7
    @10
    @6
    @0
    @6
    cc
    wcel
    #
    @4
    c1
    cc
    wcel
    #
    @0
    @11
    ax-1cn
    c1
    cA
    subcl
    mpan
    #
    adantr
    @10
    @6
    cc0
    @0
    @6
    cc0
    wceq
    #
    wn
    #
    @4
    @12
    @0
    @15
    @4
    wb
    ax-1cn
    @12
    @0
    wa
    #
    @14
    @3
    c1
    cA
    subeq0
    notbid
    mpan
    biimpar
    neqned
    #
    logcld
    imcld
    #
    3adant2
    @5
    @8
    cpi
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    @19
    cpi
    clt
    wbr
    #
    wa
    #
    @8
    cpi
    clt
    wbr
    #
    @5
    @20
    @21
    @5
    @11
    @6
    cc0
    wne
    #
    cc0
    @6
    cre
    cfv
    #
    cle
    wbr
    #
    @20
    @0
    @2
    @11
    @4
    @13
    3ad2ant1
    @0
    @4
    @24
    @2
    @17
    3adant2
    @0
    @2
    @26
    @4
    @0
    @2
    wa
    #
    cc0
    c1
    cA
    cre
    cfv
    #
    cmin
    co
    #
    @25
    cle
    @0
    @2
    @28
    c1
    cle
    wbr
    #
    cc0
    @29
    cle
    wbr
    @27
    @28
    @1
    cle
    wbr
    #
    @30
    @0
    @31
    @2
    cA
    releabs
    adantr
    @2
    @31
    @30
    wb
    @0
    @1
    c1
    @28
    cle
    breq2
    adantl
    mpbid
    @0
    @30
    wa
    #
    @28
    @28
    cmin
    co
    #
    cc0
    @29
    cle
    @0
    @33
    cc0
    wceq
    @30
    @0
    @28
    @0
    @28
    cA
    recl
    recnd
    subidd
    adantr
    @32
    @28
    c1
    @28
    @32
    cA
    @0
    @30
    simpl
    recld
    #
    @32
    1red
    @34
    @0
    @30
    simpr
    lesub1dd
    eqbrtrrd
    syldan
    @0
    @25
    @29
    wceq
    #
    @2
    @12
    @0
    @35
    ax-1cn
    @16
    @25
    c1
    cre
    cfv
    #
    @28
    cmin
    co
    @29
    c1
    cA
    resub
    @36
    c1
    @28
    cmin
    re1
    oveq1i
    syl6eq
    mpan
    adantr
    breqtrrd
    3adant3
    @11
    @24
    @26
    w3a
    @8
    @19
    cneg
    #
    @19
    cicc
    co
    wcel
    #
    @20
    @6
    argrege0
    @37
    cxr
    wcel
    @19
    cxr
    wcel
    @38
    @20
    neghalfpirx
    @19
    halfpire
    rexri
    @37
    @19
    @8
    iccleub
    mp3an12
    syl
    syl3anc
    cpi
    crp
    wcel
    @21
    pirp
    cpi
    rphalflt
    ax-mp
    jctir
    @0
    @4
    @22
    @23
    wi
    #
    @2
    @10
    @9
    @19
    cr
    wcel
    cpi
    cr
    wcel
    #
    @39
    @18
    @10
    cpi
    @40
    @10
    pire
    a1i
    #
    rehalfcld
    @41
    @8
    @19
    cpi
    lelttr
    syl3anc
    3adant2
    mpd
    ltned
end
