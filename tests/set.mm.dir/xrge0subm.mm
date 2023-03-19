include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "csubmnd.mm"
include "cfv.mm"
include "wcel.mm"
include "cxr.mm"
include "cmnf.mm"
include "csn.mm"
include "cdif.mm"
include "wss.mm"
include "cv.mm"
include "cxad.mm"
include "wral.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wne.mm"
include "simpl.mm"
include "ge0nemnf.mm"
include "jca.mm"
include "elxrge0.mm"
include "eldifsn.mm"
include "3imtr4i.mm"
include "ssriv.mm"
include "0e0iccpnf.mm"
include "ge0xaddcl.mm"
include "rgen2a.mm"
include "cmnd.mm"
include "w3a.mm"
include "wb.mm"
include "xrs1mnd.mm"
include "cbs.mm"
include "wceq.mm"
include "difss.mm"
include "cxrs.mm"
include "xrsbas.mm"
include "ressbas2.mm"
include "ax-mp.mm"
include "xrs10.mm"
include "cvv.mm"
include "cplusg.mm"
include "xrex.mm"
include "difexg.mm"
include "xrsadd.mm"
include "ressplusg.mm"
include "issubm.mm"
include "mpbir3an.mm"

theorem xrge0subm
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume xrs1mnd.1: |- R = ( RR*s |`s ( RR* \ { -oo } ) )


  assert |- ( 0 [,] +oo ) e. ( SubMnd ` R )

  proof
    cc0
    cpnf
    cicc
    co
    #
    cR
    csubmnd
    cfv
    wcel
    #
    @0
    cxr
    cmnf
    csn
    #
    cdif
    #
    wss
    #
    cc0
    @0
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cxad
    co
    @0
    wcel
    #
    vy
    @0
    wral
    vx
    @0
    wral
    #
    vx
    @0
    @3
    @6
    cxr
    wcel
    #
    cc0
    @6
    cle
    wbr
    #
    wa
    #
    @10
    @6
    cmnf
    wne
    #
    wa
    @6
    @0
    wcel
    @6
    @3
    wcel
    @12
    @10
    @13
    @10
    @11
    simpl
    @6
    ge0nemnf
    jca
    @6
    elxrge0
    @6
    cxr
    cmnf
    eldifsn
    3imtr4i
    ssriv
    0e0iccpnf
    @8
    vx
    vy
    @0
    @6
    @7
    ge0xaddcl
    rgen2a
    cR
    cmnd
    wcel
    @1
    @4
    @5
    @9
    w3a
    wb
    cR
    xrs1mnd.1
    xrs1mnd
    vx
    vy
    @3
    cxad
    @0
    cR
    cc0
    @3
    cxr
    wss
    @3
    cR
    cbs
    cfv
    wceq
    cxr
    @2
    difss
    @3
    cxr
    cR
    cxrs
    xrs1mnd.1
    xrsbas
    ressbas2
    ax-mp
    cR
    xrs1mnd.1
    xrs10
    @3
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
    @14
    xrex
    cxr
    @2
    cvv
    difexg
    ax-mp
    @3
    cxad
    cxrs
    cR
    cvv
    xrs1mnd.1
    xrsadd
    ressplusg
    ax-mp
    issubm
    ax-mp
    mpbir3an
end
