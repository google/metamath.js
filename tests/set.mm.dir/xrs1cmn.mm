include "ccmn.mm"
include "wcel.mm"
include "cmnd.mm"
include "cv.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "cxr.mm"
include "cmnf.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "xrs1mnd.mm"
include "eldifi.mm"
include "xaddcom.mm"
include "syl2an.mm"
include "rgen2a.mm"
include "wss.mm"
include "cbs.mm"
include "cfv.mm"
include "difss.mm"
include "cxrs.mm"
include "xrsbas.mm"
include "ressbas2.mm"
include "ax-mp.mm"
include "cvv.mm"
include "cplusg.mm"
include "xrex.mm"
include "difexg.mm"
include "xrsadd.mm"
include "ressplusg.mm"
include "iscmn.mm"
include "mpbir2an.mm"

theorem xrs1cmn
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume xrs1mnd.1: |- R = ( RR*s |`s ( RR* \ { -oo } ) )


  assert |- R e. CMnd

  proof
    cR
    ccmn
    wcel
    cR
    cmnd
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cxad
    co
    @1
    @0
    cxad
    co
    wceq
    #
    vy
    cxr
    cmnf
    csn
    #
    cdif
    #
    wral
    vx
    @4
    wral
    cR
    xrs1mnd.1
    xrs1mnd
    @2
    vx
    vy
    @4
    @0
    @4
    wcel
    @0
    cxr
    wcel
    @1
    cxr
    wcel
    @2
    @1
    @4
    wcel
    @0
    cxr
    @3
    eldifi
    @1
    cxr
    @3
    eldifi
    @0
    @1
    xaddcom
    syl2an
    rgen2a
    vx
    vy
    @4
    cxad
    cR
    @4
    cxr
    wss
    @4
    cR
    cbs
    cfv
    wceq
    cxr
    @3
    difss
    @4
    cxr
    cR
    cxrs
    xrs1mnd.1
    xrsbas
    ressbas2
    ax-mp
    @4
    cvv
    wcel
    #
    cxad
    cR
    cplusg
    cfv
    wceq
    cxr
    cvv
    wcel
    @5
    xrex
    cxr
    @3
    cvv
    difexg
    ax-mp
    @4
    cxad
    cxrs
    cR
    cvv
    xrs1mnd.1
    xrsadd
    ressplusg
    ax-mp
    iscmn
    mpbir2an
end
