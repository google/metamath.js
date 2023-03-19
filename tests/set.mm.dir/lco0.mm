include "cmnd.mm"
include "wcel.mm"
include "c0.mm"
include "clinco.mm"
include "co.mm"
include "cv.mm"
include "csca.mm"
include "cfv.mm"
include "c0g.mm"
include "cfsupp.mm"
include "wbr.mm"
include "clinc.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "cmap.mm"
include "wrex.mm"
include "crab.mm"
include "csn.mm"
include "cpw.mm"
include "0elpw.mm"
include "eqid.mm"
include "lcoop.mm"
include "mpan2.mm"
include "c1o.mm"
include "cvv.mm"
include "fvex.mm"
include "map0e.mm"
include "mp1i.mm"
include "df1o2.mm"
include "syl6eq.mm"
include "rexeqdv.mm"
include "cfn.mm"
include "lincval0.mm"
include "adantr.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "wb.mm"
include "0ex.mm"
include "breq1.mm"
include "0fsupp.mm"
include "ax-mp.mm"
include "0fin.mm"
include "2th.mm"
include "syl6bb.mm"
include "oveq1.mm"
include "anbi12d.mm"
include "rexsng.mm"
include "a1i.mm"
include "biantrurd.mm"
include "3bitr4d.mm"
include "bitrd.mm"
include "rabbidva.mm"
include "mndidcl.mm"
include "rabsn.mm"
include "syl.mm"
include "3eqtrd.mm"

theorem lco0
  let cM: class M
  let vv: setvar v
  let vw: setvar w
  let vk: setvar k
  let vx: setvar x


  assert |- ( M e. Mnd -> ( M LinCo (/) ) = { ( 0g ` M ) } )

  proof
    cM
    cmnd
    wcel
    #
    cM
    c0
    clinco
    co
    #
    vw
    cv
    #
    cM
    csca
    cfv
    #
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    vv
    cv
    #
    @2
    c0
    cM
    clinc
    cfv
    #
    co
    #
    wceq
    #
    wa
    #
    vw
    @3
    cbs
    cfv
    #
    c0
    cmap
    co
    #
    wrex
    #
    vv
    cM
    cbs
    cfv
    #
    crab
    #
    @6
    cM
    c0g
    cfv
    #
    wceq
    #
    vv
    @14
    crab
    #
    @16
    csn
    #
    @0
    c0
    @14
    cpw
    wcel
    @1
    @15
    wceq
    @14
    0elpw
    @14
    @11
    @3
    cM
    c0
    cmnd
    vw
    vv
    @14
    eqid
    #
    @3
    eqid
    @11
    eqid
    lcoop
    mpan2
    @0
    @13
    @17
    vv
    @14
    @0
    @6
    @14
    wcel
    #
    wa
    #
    @13
    @10
    vw
    c0
    csn
    #
    wrex
    #
    @17
    @22
    @10
    vw
    @12
    @23
    @22
    @12
    c1o
    @23
    @11
    cvv
    wcel
    @12
    c1o
    wceq
    @22
    @3
    cbs
    fvex
    @11
    cvv
    map0e
    mp1i
    df1o2
    syl6eq
    rexeqdv
    @22
    c0
    cfn
    wcel
    #
    @6
    c0
    c0
    @7
    co
    #
    wceq
    #
    wa
    #
    @25
    @17
    wa
    @24
    @17
    @22
    @27
    @17
    @25
    @22
    @26
    @16
    @6
    @0
    @26
    @16
    wceq
    @21
    cM
    cmnd
    lincval0
    adantr
    eqeq2d
    anbi2d
    c0
    cvv
    wcel
    @24
    @28
    wb
    @22
    0ex
    @10
    @28
    vw
    c0
    cvv
    @2
    c0
    wceq
    #
    @5
    @25
    @9
    @27
    @29
    @5
    c0
    @4
    cfsupp
    wbr
    #
    @25
    @2
    c0
    @4
    cfsupp
    breq1
    @30
    @25
    @4
    cvv
    wcel
    @30
    @3
    c0g
    fvex
    cvv
    @4
    0fsupp
    ax-mp
    0fin
    2th
    syl6bb
    @29
    @8
    @26
    @6
    @2
    c0
    c0
    @7
    oveq1
    eqeq2d
    anbi12d
    rexsng
    mp1i
    @22
    @25
    @17
    @25
    @22
    0fin
    a1i
    biantrurd
    3bitr4d
    bitrd
    rabbidva
    @0
    @16
    @14
    wcel
    @18
    @19
    wceq
    @14
    cM
    @16
    @20
    @16
    eqid
    mndidcl
    vv
    @14
    @16
    rabsn
    syl
    3eqtrd
end
