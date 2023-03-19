include "cr.mm"
include "wcel.mm"
include "cmnf.mm"
include "cioc.mm"
include "co.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "ccld.mm"
include "cdif.mm"
include "cpnf.mm"
include "cun.mm"
include "wceq.mm"
include "cxr.mm"
include "clt.mm"
include "wbr.mm"
include "mnfxr.mm"
include "a1i.mm"
include "rexr.mm"
include "pnfxr.mm"
include "mnflt.mm"
include "ltpnf.mm"
include "cle.mm"
include "df-ioc.mm"
include "df-ioo.mm"
include "cv.mm"
include "xrltnle.mm"
include "xrlelttr.mm"
include "xrlttr.mm"
include "ixxun.mm"
include "syl32anc.mm"
include "ioomax.mm"
include "syl6eq.mm"
include "wss.mm"
include "cin.mm"
include "c0.mm"
include "wb.mm"
include "iocssre.mm"
include "mpan.mm"
include "ixxdisj.mm"
include "syl3anc.mm"
include "uneqdifeq.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "iooretop.mm"
include "syl6eqel.mm"
include "ctop.mm"
include "retop.mm"
include "uniretop.mm"
include "iscld2.mm"
include "sylancr.mm"
include "mpbird.mm"

theorem iocmnfcld
  let cA: class A
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. RR -> ( -oo (,] A ) e. ( Clsd ` ( topGen ` ran (,) ) ) )

  proof
    cA
    cr
    wcel
    #
    cmnf
    cA
    cioc
    co
    #
    cioo
    crn
    ctg
    cfv
    #
    ccld
    cfv
    wcel
    #
    cr
    @1
    cdif
    #
    @2
    wcel
    #
    @0
    @4
    cA
    cpnf
    cioo
    co
    #
    @2
    @0
    @1
    @6
    cun
    #
    cr
    wceq
    #
    @4
    @6
    wceq
    #
    @0
    @7
    cmnf
    cpnf
    cioo
    co
    #
    cr
    @0
    cmnf
    cxr
    wcel
    #
    cA
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    cmnf
    cA
    clt
    wbr
    cA
    cpnf
    clt
    wbr
    @7
    @10
    wceq
    @11
    @0
    mnfxr
    a1i
    #
    cA
    rexr
    #
    @13
    @0
    pnfxr
    a1i
    #
    cA
    mnflt
    cA
    ltpnf
    vx
    vy
    vz
    vw
    cmnf
    cA
    cpnf
    cioo
    cioo
    clt
    cle
    clt
    clt
    cioc
    clt
    clt
    vx
    vy
    vz
    df-ioc
    #
    vx
    vy
    vz
    df-ioo
    #
    cA
    vw
    cv
    #
    xrltnle
    #
    @18
    @19
    cA
    cpnf
    xrlelttr
    cmnf
    cA
    @19
    xrlttr
    ixxun
    syl32anc
    ioomax
    syl6eq
    @0
    @1
    cr
    wss
    #
    @1
    @6
    cin
    c0
    wceq
    #
    @8
    @9
    wb
    @11
    @0
    @21
    mnfxr
    cmnf
    cA
    iocssre
    mpan
    #
    @0
    @11
    @12
    @13
    @22
    @14
    @15
    @16
    vx
    vy
    vz
    vw
    cmnf
    cA
    cpnf
    cioo
    clt
    cle
    clt
    clt
    cioc
    @17
    @18
    @20
    ixxdisj
    syl3anc
    @1
    @6
    cr
    uneqdifeq
    syl2anc
    mpbid
    cA
    cpnf
    iooretop
    syl6eqel
    @0
    @2
    ctop
    wcel
    @21
    @3
    @5
    wb
    retop
    @23
    @1
    @2
    cr
    uniretop
    iscld2
    sylancr
    mpbird
end
