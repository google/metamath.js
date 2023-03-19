include "cc.mm"
include "wcel.mm"
include "cim.mm"
include "cfv.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "clog.mm"
include "cr.mm"
include "cpi.mm"
include "cneg.mm"
include "cioo.mm"
include "co.mm"
include "wne.mm"
include "simpr.mm"
include "lt0ne0d.mm"
include "wceq.mm"
include "fveq2.mm"
include "im0.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "syl.mm"
include "logcl.mm"
include "syldan.mm"
include "imcld.mm"
include "ccj.mm"
include "logcj.mm"
include "fveq2d.mm"
include "imcjd.mm"
include "eqtrd.mm"
include "cjcl.mm"
include "adantr.mm"
include "imcl.mm"
include "lt0neg1d.mm"
include "mpbid.mm"
include "imcj.mm"
include "breqtrrd.mm"
include "argimgt0.mm"
include "syl2anc.mm"
include "eliooord.mm"
include "simprd.mm"
include "eqbrtrrd.mm"
include "wb.mm"
include "pire.mm"
include "ltnegcon1.mm"
include "sylancl.mm"
include "simpld.mm"
include "breqtrd.mm"
include "mpbird.mm"
include "cxr.mm"
include "w3a.mm"
include "renegcli.mm"
include "rexri.mm"
include "0xr.mm"
include "elioo2.mm"
include "mp2an.mm"
include "syl3anbrc.mm"

theorem argimlt0
  let cA: class A


  assert |- ( ( A e. CC /\ ( Im ` A ) < 0 ) -> ( Im ` ( log ` A ) ) e. ( -u _pi (,) 0 ) )

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
    clt
    wbr
    #
    wa
    #
    cA
    clog
    cfv
    #
    cim
    cfv
    #
    cr
    wcel
    #
    cpi
    cneg
    #
    @5
    clt
    wbr
    #
    @5
    cc0
    clt
    wbr
    #
    @5
    @7
    cc0
    cioo
    co
    wcel
    #
    @3
    @4
    @0
    @2
    cA
    cc0
    wne
    #
    @4
    cc
    wcel
    @3
    @1
    cc0
    wne
    #
    @11
    @3
    @1
    @0
    @2
    simpr
    #
    lt0ne0d
    #
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
    syl
    cA
    logcl
    syldan
    #
    imcld
    #
    @3
    @5
    cneg
    #
    cpi
    clt
    wbr
    #
    @8
    @3
    cA
    ccj
    cfv
    #
    clog
    cfv
    #
    cim
    cfv
    #
    @17
    cpi
    clt
    @3
    @21
    @4
    ccj
    cfv
    #
    cim
    cfv
    @17
    @3
    @20
    @22
    cim
    @0
    @2
    @12
    @20
    @22
    wceq
    @14
    cA
    logcj
    syldan
    fveq2d
    @3
    @4
    @15
    imcjd
    eqtrd
    #
    @3
    cc0
    @21
    clt
    wbr
    #
    @21
    cpi
    clt
    wbr
    #
    @3
    @21
    cc0
    cpi
    cioo
    co
    wcel
    #
    @24
    @25
    wa
    @3
    @19
    cc
    wcel
    #
    cc0
    @19
    cim
    cfv
    #
    clt
    wbr
    @26
    @0
    @27
    @2
    cA
    cjcl
    adantr
    @3
    cc0
    @1
    cneg
    #
    @28
    clt
    @3
    @2
    cc0
    @29
    clt
    wbr
    @13
    @3
    @1
    @0
    @1
    cr
    wcel
    @2
    cA
    imcl
    adantr
    lt0neg1d
    mpbid
    @0
    @28
    @29
    wceq
    @2
    cA
    imcj
    adantr
    breqtrrd
    @19
    argimgt0
    syl2anc
    @21
    cc0
    cpi
    eliooord
    syl
    #
    simprd
    eqbrtrrd
    @3
    @6
    cpi
    cr
    wcel
    @18
    @8
    wb
    @16
    pire
    @5
    cpi
    ltnegcon1
    sylancl
    mpbid
    @3
    @9
    cc0
    @17
    clt
    wbr
    @3
    cc0
    @21
    @17
    clt
    @3
    @24
    @25
    @30
    simpld
    @23
    breqtrd
    @3
    @5
    @16
    lt0neg1d
    mpbird
    @7
    cxr
    wcel
    cc0
    cxr
    wcel
    @10
    @6
    @8
    @9
    w3a
    wb
    @7
    cpi
    pire
    renegcli
    rexri
    0xr
    @7
    cc0
    @5
    elioo2
    mp2an
    syl3anbrc
end
