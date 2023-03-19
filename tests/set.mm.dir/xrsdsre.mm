include "cr.mm"
include "cxp.mm"
include "cres.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "xrsdsreval.mm"
include "ovres.mm"
include "eqid.mm"
include "remetdval.mm"
include "3eqtr4d.mm"
include "rgen2a.mm"
include "wfn.mm"
include "wb.mm"
include "cxr.mm"
include "wss.mm"
include "cxmt.mm"
include "wf.mm"
include "xrsxmet.mm"
include "xmetf.mm"
include "ffn.mm"
include "mp2b.mm"
include "rexpssxrxp.mm"
include "fnssres.mm"
include "mp2an.mm"
include "cc.mm"
include "cme.mm"
include "cnmet.mm"
include "metf.mm"
include "ax-resscn.mm"
include "xpss12.mm"
include "eqfnov2.mm"
include "mpbir.mm"

theorem xrsdsre
  let cD: class D
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cJ: class J
  let cP: class P
  let cR: class R
  assume xrsxmet.1: |- D = ( dist ` RR*s )


  assert |- ( D |` ( RR X. RR ) ) = ( ( abs o. - ) |` ( RR X. RR ) )

  proof
    cD
    cr
    cr
    cxp
    #
    cres
    #
    cabs
    cmin
    ccom
    #
    @0
    cres
    #
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    @1
    co
    #
    @5
    @6
    @3
    co
    #
    wceq
    #
    vy
    cr
    wral
    vx
    cr
    wral
    #
    @9
    vx
    vy
    cr
    @5
    cr
    wcel
    @6
    cr
    wcel
    wa
    @5
    @6
    cD
    co
    @5
    @6
    cmin
    co
    cabs
    cfv
    @7
    @8
    @5
    @6
    cD
    xrsxmet.1
    xrsdsreval
    @5
    @6
    cr
    cr
    cD
    ovres
    @5
    @6
    @3
    @3
    eqid
    remetdval
    3eqtr4d
    rgen2a
    @1
    @0
    wfn
    #
    @3
    @0
    wfn
    #
    @4
    @10
    wb
    cD
    cxr
    cxr
    cxp
    #
    wfn
    #
    @0
    @13
    wss
    @11
    cD
    cxr
    cxmt
    cfv
    wcel
    @13
    cxr
    cD
    wf
    @14
    cD
    xrsxmet.1
    xrsxmet
    cD
    cxr
    xmetf
    @13
    cxr
    cD
    ffn
    mp2b
    rexpssxrxp
    @13
    @0
    cD
    fnssres
    mp2an
    @2
    cc
    cc
    cxp
    #
    wfn
    #
    @0
    @15
    wss
    #
    @12
    @2
    cc
    cme
    cfv
    wcel
    @15
    cr
    @2
    wf
    @16
    cnmet
    @2
    cc
    metf
    @15
    cr
    @2
    ffn
    mp2b
    cr
    cc
    wss
    #
    @18
    @17
    ax-resscn
    ax-resscn
    cr
    cc
    cr
    cc
    xpss12
    mp2an
    @15
    @0
    @2
    fnssres
    mp2an
    vx
    vy
    cr
    cr
    @1
    @3
    eqfnov2
    mp2an
    mpbir
end
