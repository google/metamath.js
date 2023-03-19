include "cxrs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cress.mm"
include "ctmd.mm"
include "wcel.mm"
include "cmnd.mm"
include "ctps.mm"
include "cxad.mm"
include "cxp.mm"
include "cres.mm"
include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "crest.mm"
include "ctx.mm"
include "ccn.mm"
include "ccmn.mm"
include "xrge0cmn.mm"
include "cmnmnd.mm"
include "ax-mp.mm"
include "xrge0tps.mm"
include "c1.mm"
include "cv.mm"
include "wceq.mm"
include "clog.mm"
include "cneg.mm"
include "cif.mm"
include "cmpt.mm"
include "eqeq1.mm"
include "fveq2.mm"
include "negeqd.mm"
include "ifbieq2d.mm"
include "cbvmptv.mm"
include "eqid.mm"
include "xrge0pluscn.mm"
include "cplusf.mm"
include "cxr.mm"
include "xrsbas.mm"
include "xrsadd.mm"
include "wf.mm"
include "wfn.mm"
include "xaddf.mm"
include "ffn.mm"
include "iccssxr.mm"
include "ressplusf.mm"
include "eqcomi.mm"
include "xrge0base.mm"
include "cvv.mm"
include "cts.mm"
include "ovex.mm"
include "xrstset.mm"
include "resstset.mm"
include "topnval.mm"
include "istmd.mm"
include "mpbir3an.mm"

theorem xrge0tmdOLD
  let vx: setvar x
  let vy: setvar y


  assert |- ( RR*s |`s ( 0 [,] +oo ) ) e. TopMnd

  proof
    cxrs
    cc0
    cpnf
    cicc
    co
    #
    cress
    co
    #
    ctmd
    wcel
    @1
    cmnd
    wcel
    #
    @1
    ctps
    wcel
    cxad
    @0
    @0
    cxp
    cres
    #
    cle
    cordt
    cfv
    #
    @0
    crest
    co
    #
    @5
    ctx
    co
    @5
    ccn
    co
    wcel
    @1
    ccmn
    wcel
    @2
    xrge0cmn
    @1
    cmnmnd
    ax-mp
    xrge0tps
    vx
    @3
    vy
    cc0
    c1
    cicc
    co
    #
    vy
    cv
    #
    cc0
    wceq
    #
    cpnf
    @7
    clog
    cfv
    #
    cneg
    #
    cif
    #
    cmpt
    @5
    vy
    vx
    @6
    @11
    vx
    cv
    #
    cc0
    wceq
    #
    cpnf
    @12
    clog
    cfv
    #
    cneg
    #
    cif
    @7
    @12
    wceq
    #
    @8
    @13
    @10
    @15
    cpnf
    @7
    @12
    cc0
    eqeq1
    @16
    @9
    @14
    @7
    @12
    clog
    fveq2
    negeqd
    ifbieq2d
    cbvmptv
    @5
    eqid
    @3
    eqid
    xrge0pluscn
    @3
    @1
    @5
    @1
    cplusf
    cfv
    @3
    @0
    cxr
    cxad
    cxrs
    @1
    xrsbas
    @1
    eqid
    #
    xrsadd
    cxr
    cxr
    cxp
    #
    cxr
    cxad
    wf
    cxad
    @18
    wfn
    xaddf
    @18
    cxr
    cxad
    ffn
    ax-mp
    cc0
    cpnf
    iccssxr
    ressplusf
    eqcomi
    @0
    @4
    @1
    xrge0base
    @0
    cvv
    wcel
    @4
    @1
    cts
    cfv
    wceq
    cc0
    cpnf
    cicc
    ovex
    @0
    cxrs
    @1
    @4
    cvv
    @17
    xrstset
    resstset
    ax-mp
    topnval
    istmd
    mpbir3an
end
