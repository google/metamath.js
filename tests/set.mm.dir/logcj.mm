include "cc.mm"
include "wcel.mm"
include "cim.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "ccj.mm"
include "clog.mm"
include "wceq.mm"
include "ce.mm"
include "fveq2.mm"
include "im0.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "logcl.mm"
include "sylan2.mm"
include "efcj.mm"
include "syl.mm"
include "eflog.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "crn.mm"
include "wb.mm"
include "cjcl.mm"
include "adantr.mm"
include "simpr.mm"
include "cjne0.mm"
include "mpbid.mm"
include "cpi.mm"
include "cneg.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "cjcld.mm"
include "crp.mm"
include "cr.mm"
include "rpre.mm"
include "renegcld.mm"
include "negneg.mm"
include "eleq1d.mm"
include "syl5ib.mm"
include "lognegb.mm"
include "reim0b.mm"
include "3imtr3d.mm"
include "necon3d.mm"
include "mpd.mm"
include "necomd.mm"
include "imcld.mm"
include "pire.mm"
include "a1i.mm"
include "logimcl.mm"
include "simprd.mm"
include "leltned.mm"
include "mpbird.mm"
include "ltneg.mm"
include "sylancl.mm"
include "imcjd.mm"
include "breqtrrd.mm"
include "simpld.mm"
include "wi.mm"
include "renegcli.mm"
include "ltle.mm"
include "sylancr.mm"
include "lenegcon1.mm"
include "eqbrtrd.mm"
include "ellogrn.mm"
include "syl3anbrc.mm"
include "logeftb.mm"
include "syl3anc.mm"

theorem logcj
  let cA: class A


  assert |- ( ( A e. CC /\ ( Im ` A ) =/= 0 ) -> ( log ` ( * ` A ) ) = ( * ` ( log ` A ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cim
    cfv
    #
    cc0
    wne
    #
    wa
    #
    cA
    ccj
    cfv
    #
    clog
    cfv
    cA
    clog
    cfv
    #
    ccj
    cfv
    #
    wceq
    #
    @6
    ce
    cfv
    #
    @4
    wceq
    #
    @3
    @8
    @5
    ce
    cfv
    #
    ccj
    cfv
    #
    @4
    @3
    @5
    cc
    wcel
    #
    @8
    @11
    wceq
    @2
    @0
    cA
    cc0
    wne
    #
    @12
    cA
    cc0
    @1
    cc0
    cA
    cc0
    wceq
    @1
    cc0
    cim
    cfv
    cc0
    cA
    cc0
    cim
    fveq2
    im0
    syl6eq
    necon3i
    #
    cA
    logcl
    sylan2
    #
    @5
    efcj
    syl
    @3
    @10
    cA
    ccj
    @2
    @0
    @13
    @10
    cA
    wceq
    @14
    cA
    eflog
    sylan2
    fveq2d
    eqtrd
    @3
    @4
    cc
    wcel
    #
    @4
    cc0
    wne
    #
    @6
    clog
    crn
    wcel
    #
    @7
    @9
    wb
    @0
    @16
    @2
    cA
    cjcl
    adantr
    @3
    @13
    @17
    @3
    @2
    @13
    @0
    @2
    simpr
    #
    @14
    syl
    @0
    @13
    @17
    wb
    @2
    cA
    cjne0
    adantr
    mpbid
    @3
    @6
    cc
    wcel
    cpi
    cneg
    #
    @6
    cim
    cfv
    #
    clt
    wbr
    @21
    cpi
    cle
    wbr
    @18
    @3
    @5
    @15
    cjcld
    @3
    @20
    @5
    cim
    cfv
    #
    cneg
    #
    @21
    clt
    @3
    @22
    cpi
    clt
    wbr
    #
    @20
    @23
    clt
    wbr
    #
    @3
    @24
    cpi
    @22
    wne
    @3
    @22
    cpi
    @3
    @2
    @22
    cpi
    wne
    @19
    @3
    @22
    cpi
    @1
    cc0
    @3
    cA
    cneg
    #
    crp
    wcel
    #
    cA
    cr
    wcel
    #
    @22
    cpi
    wceq
    #
    @1
    cc0
    wceq
    #
    @27
    @26
    cneg
    #
    cr
    wcel
    @3
    @28
    @27
    @26
    @26
    rpre
    renegcld
    @3
    @31
    cA
    cr
    @0
    @31
    cA
    wceq
    @2
    cA
    negneg
    adantr
    eleq1d
    syl5ib
    @2
    @0
    @13
    @27
    @29
    wb
    @14
    cA
    lognegb
    sylan2
    @0
    @28
    @30
    wb
    @2
    cA
    reim0b
    adantr
    3imtr3d
    necon3d
    mpd
    necomd
    @3
    @22
    cpi
    @3
    @5
    @15
    imcld
    #
    cpi
    cr
    wcel
    #
    @3
    pire
    a1i
    @3
    @20
    @22
    clt
    wbr
    #
    @22
    cpi
    cle
    wbr
    #
    @2
    @0
    @13
    @34
    @35
    wa
    @14
    cA
    logimcl
    sylan2
    #
    simprd
    leltned
    mpbird
    @3
    @22
    cr
    wcel
    #
    @33
    @24
    @25
    wb
    @32
    pire
    @22
    cpi
    ltneg
    sylancl
    mpbid
    @3
    @5
    @15
    imcjd
    #
    breqtrrd
    @3
    @21
    @23
    cpi
    cle
    @38
    @3
    @20
    @22
    cle
    wbr
    #
    @23
    cpi
    cle
    wbr
    #
    @3
    @34
    @39
    @3
    @34
    @35
    @36
    simpld
    @3
    @20
    cr
    wcel
    @37
    @34
    @39
    wi
    cpi
    pire
    renegcli
    @32
    @20
    @22
    ltle
    sylancr
    mpd
    @3
    @33
    @37
    @39
    @40
    wb
    pire
    @32
    cpi
    @22
    lenegcon1
    sylancr
    mpbid
    eqbrtrd
    @6
    ellogrn
    syl3anbrc
    @4
    @6
    logeftb
    syl3anc
    mpbird
end
