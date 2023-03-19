include "cr.mm"
include "wcel.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cmnf.mm"
include "cioo.mm"
include "cdif.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "ccld.mm"
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
include "df-ioo.mm"
include "df-ico.mm"
include "cv.mm"
include "xrlenlt.mm"
include "xrlttr.mm"
include "xrltletr.mm"
include "ixxun.mm"
include "syl32anc.mm"
include "ioomax.mm"
include "syl6eq.mm"
include "wss.mm"
include "cin.mm"
include "c0.mm"
include "wb.mm"
include "ioossre.mm"
include "ixxdisj.mm"
include "syl3anc.mm"
include "uneqdifeq.mm"
include "sylancr.mm"
include "mpbid.mm"
include "ctop.mm"
include "retop.mm"
include "iooretop.mm"
include "uniretop.mm"
include "opncld.mm"
include "mp2an.mm"
include "syl6eqelr.mm"

theorem icopnfcld
  let cA: class A
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. RR -> ( A [,) +oo ) e. ( Clsd ` ( topGen ` ran (,) ) ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cpnf
    cico
    co
    #
    cr
    cmnf
    cA
    cioo
    co
    #
    cdif
    #
    cioo
    crn
    ctg
    cfv
    #
    ccld
    cfv
    #
    @0
    @2
    @1
    cun
    #
    cr
    wceq
    #
    @3
    @1
    wceq
    #
    @0
    @6
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
    @6
    @9
    wceq
    @10
    @0
    mnfxr
    a1i
    #
    cA
    rexr
    #
    @12
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
    cico
    cioo
    clt
    clt
    cle
    clt
    cioo
    clt
    clt
    vx
    vy
    vz
    df-ioo
    #
    vx
    vy
    vz
    df-ico
    #
    cA
    vw
    cv
    #
    xrlenlt
    #
    @16
    @18
    cA
    cpnf
    xrlttr
    cmnf
    cA
    @18
    xrltletr
    ixxun
    syl32anc
    ioomax
    syl6eq
    @0
    @2
    cr
    wss
    @2
    @1
    cin
    c0
    wceq
    #
    @7
    @8
    wb
    cmnf
    cA
    ioossre
    @0
    @10
    @11
    @12
    @20
    @13
    @14
    @15
    vx
    vy
    vz
    vw
    cmnf
    cA
    cpnf
    cico
    clt
    clt
    cle
    clt
    cioo
    @16
    @17
    @19
    ixxdisj
    syl3anc
    @2
    @1
    cr
    uneqdifeq
    sylancr
    mpbid
    @4
    ctop
    wcel
    @2
    @4
    wcel
    @3
    @5
    wcel
    retop
    cmnf
    cA
    iooretop
    @2
    @4
    cr
    uniretop
    opncld
    mp2an
    syl6eqelr
end
