include "c1.mm"
include "cclwwlkn.mm"
include "co.mm"
include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "cword.mm"
include "cv.mm"
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
include "csn.mm"
include "cn.mm"
include "wb.mm"
include "1nn.mm"
include "eqid.mm"
include "isclwwlknx.mm"
include "ax-mp.mm"
include "3anass.mm"
include "c0.mm"
include "ral0.mm"
include "oveq1.mm"
include "1m1e0.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "fzo0.mm"
include "raleqdv.mm"
include "adantr.mm"
include "mpbiri.mm"
include "biantrurd.mm"
include "lsw1.mm"
include "ancoms.mm"
include "preq1d.mm"
include "dfsn2.mm"
include "syl6eqr.mm"
include "eleq1d.mm"
include "bitr3d.mm"
include "pm5.32da.mm"
include "syl5bb.mm"
include "pm5.32ri.mm"
include "ancom.mm"
include "bitr2i.mm"
include "3bitri.mm"

theorem clwwlkn1
  let cG: class G
  let cW: class W
  let vi: setvar i


  assert |- ( W e. ( 1 ClWWalksN G ) <-> ( ( # ` W ) = 1 /\ W e. Word ( Vtx ` G ) /\ { ( W ` 0 ) } e. ( Edg ` G ) ) )

  proof
    cW
    c1
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
    wcel
    #
    vi
    cv
    #
    cW
    cfv
    @3
    c1
    caddc
    co
    cW
    cfv
    cpr
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
    @4
    wcel
    #
    w3a
    #
    @6
    c1
    wceq
    #
    wa
    #
    @2
    @11
    csn
    #
    @4
    wcel
    #
    wa
    #
    @15
    wa
    #
    @15
    @2
    @18
    w3a
    #
    c1
    cn
    wcel
    @0
    @16
    wb
    1nn
    vi
    @4
    cG
    c1
    @1
    cW
    @1
    eqid
    @4
    eqid
    isclwwlknx
    ax-mp
    @15
    @14
    @19
    @14
    @2
    @9
    @13
    wa
    #
    wa
    @15
    @19
    @2
    @9
    @13
    3anass
    @15
    @2
    @22
    @18
    @15
    @2
    wa
    #
    @13
    @22
    @18
    @23
    @9
    @13
    @23
    @9
    @5
    vi
    c0
    wral
    #
    @5
    vi
    ral0
    @15
    @9
    @24
    wb
    @2
    @15
    @5
    vi
    @8
    c0
    @15
    @8
    cc0
    cc0
    cfzo
    co
    c0
    @15
    @7
    cc0
    cc0
    cfzo
    @15
    @7
    c1
    c1
    cmin
    co
    cc0
    @6
    c1
    c1
    cmin
    oveq1
    1m1e0
    syl6eq
    oveq2d
    cc0
    fzo0
    syl6eq
    raleqdv
    adantr
    mpbiri
    biantrurd
    @23
    @12
    @17
    @4
    @23
    @12
    @11
    @11
    cpr
    @17
    @23
    @10
    @11
    @11
    @2
    @15
    @10
    @11
    wceq
    @1
    cW
    lsw1
    ancoms
    preq1d
    @11
    dfsn2
    syl6eqr
    eleq1d
    bitr3d
    pm5.32da
    syl5bb
    pm5.32ri
    @21
    @15
    @19
    wa
    @20
    @15
    @2
    @18
    3anass
    @15
    @19
    ancom
    bitr2i
    3bitri
end
