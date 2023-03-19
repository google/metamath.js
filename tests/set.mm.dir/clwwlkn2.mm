include "c2.mm"
include "cclwwlkn.mm"
include "co.mm"
include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "cword.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "cedg.mm"
include "cc0.mm"
include "chash.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "clsw.mm"
include "w3a.mm"
include "wceq.mm"
include "wa.mm"
include "cn.mm"
include "wb.mm"
include "2nn.mm"
include "eqid.mm"
include "isclwwlknx.mm"
include "ax-mp.mm"
include "3anass.mm"
include "csn.mm"
include "oveq1.mm"
include "2m1e1.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "fzo01.mm"
include "adantr.mm"
include "raleqdv.mm"
include "c0ex.mm"
include "fveq2.mm"
include "0p1e1.mm"
include "fveq2d.mm"
include "preq12d.mm"
include "eleq1d.mm"
include "ralsn.mm"
include "syl6bb.mm"
include "prcom.mm"
include "lsw.mm"
include "sylan9eqr.mm"
include "preq2d.mm"
include "syl5eq.mm"
include "anbi12d.mm"
include "anidm.mm"
include "pm5.32da.mm"
include "syl5bb.mm"
include "pm5.32ri.mm"
include "ancom.mm"
include "bitr2i.mm"
include "3bitri.mm"

theorem clwwlkn2
  let cG: class G
  let cW: class W
  let vi: setvar i


  assert |- ( W e. ( 2 ClWWalksN G ) <-> ( ( # ` W ) = 2 /\ W e. Word ( Vtx ` G ) /\ { ( W ` 0 ) , ( W ` 1 ) } e. ( Edg ` G ) ) )

  proof
    cW
    c2
    cG
    cclwwlkn
    co
    wcel
    #
    cW
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    vi
    cv
    #
    cW
    cfv
    #
    @4
    c1
    caddc
    co
    #
    cW
    cfv
    #
    cpr
    #
    cG
    cedg
    cfv
    #
    wcel
    #
    vi
    cc0
    cW
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    cW
    clsw
    cfv
    #
    cc0
    cW
    cfv
    #
    cpr
    #
    @9
    wcel
    #
    w3a
    #
    @11
    c2
    wceq
    #
    wa
    #
    @3
    @16
    c1
    cW
    cfv
    #
    cpr
    #
    @9
    wcel
    #
    wa
    #
    @20
    wa
    #
    @20
    @3
    @24
    w3a
    #
    c2
    cn
    wcel
    @0
    @21
    wb
    2nn
    vi
    @9
    cG
    c2
    @1
    cW
    @1
    eqid
    @9
    eqid
    isclwwlknx
    ax-mp
    @20
    @19
    @25
    @19
    @3
    @14
    @18
    wa
    #
    wa
    @20
    @25
    @3
    @14
    @18
    3anass
    @20
    @3
    @28
    @24
    @20
    @3
    wa
    #
    @28
    @24
    @24
    wa
    @24
    @29
    @14
    @24
    @18
    @24
    @29
    @14
    @10
    vi
    cc0
    csn
    #
    wral
    @24
    @29
    @10
    vi
    @13
    @30
    @20
    @13
    @30
    wceq
    @3
    @20
    @13
    cc0
    c1
    cfzo
    co
    @30
    @20
    @12
    c1
    cc0
    cfzo
    @20
    @12
    c2
    c1
    cmin
    co
    c1
    @11
    c2
    c1
    cmin
    oveq1
    2m1e1
    syl6eq
    #
    oveq2d
    fzo01
    syl6eq
    adantr
    raleqdv
    @10
    @24
    vi
    cc0
    c0ex
    @4
    cc0
    wceq
    #
    @8
    @23
    @9
    @32
    @5
    @16
    @7
    @22
    @4
    cc0
    cW
    fveq2
    @32
    @6
    c1
    cW
    @32
    @6
    cc0
    c1
    caddc
    co
    c1
    @4
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    fveq2d
    preq12d
    eleq1d
    ralsn
    syl6bb
    @29
    @17
    @23
    @9
    @29
    @17
    @16
    @15
    cpr
    @23
    @15
    @16
    prcom
    @29
    @15
    @22
    @16
    @3
    @20
    @15
    @12
    cW
    cfv
    @22
    cW
    @2
    lsw
    @20
    @12
    c1
    cW
    @31
    fveq2d
    sylan9eqr
    preq2d
    syl5eq
    eleq1d
    anbi12d
    @24
    anidm
    syl6bb
    pm5.32da
    syl5bb
    pm5.32ri
    @27
    @20
    @25
    wa
    @26
    @20
    @3
    @24
    3anass
    @20
    @25
    ancom
    bitr2i
    3bitri
end
