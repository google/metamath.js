include "ccnfld.mm"
include "cmgp.mm"
include "cfv.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cress.mm"
include "cxrs.mm"
include "cpnf.mm"
include "cv.mm"
include "wceq.mm"
include "clog.mm"
include "cneg.mm"
include "cif.mm"
include "cmpt.mm"
include "ctopn.mm"
include "eqeq1.mm"
include "fveq2.mm"
include "negeqd.mm"
include "ifbieq2d.mm"
include "cbvmptv.mm"
include "xrge0topn.mm"
include "xrge0iifmhm.mm"
include "cii.mm"
include "chmeo.mm"
include "xrge0iifhmeo.mm"
include "cvv.mm"
include "wcel.mm"
include "cnfldex.mm"
include "ovex.mm"
include "eqid.mm"
include "mgpress.mm"
include "mp2an.mm"
include "dfii4.mm"
include "mgptopn.mm"
include "oveq1i.mm"
include "eleqtri.mm"
include "iistmd.mm"
include "xrge0tps.mm"
include "mhmhmeotmd.mm"

theorem xrge0tmd
  let vx: setvar x
  let vy: setvar y


  assert |- ( RR*s |`s ( 0 [,] +oo ) ) e. TopMnd

  proof
    ccnfld
    cmgp
    cfv
    #
    cc0
    c1
    cicc
    co
    #
    cress
    co
    #
    cxrs
    cc0
    cpnf
    cicc
    co
    cress
    co
    #
    vx
    @1
    vx
    cv
    #
    cc0
    wceq
    #
    cpnf
    @4
    clog
    cfv
    #
    cneg
    #
    cif
    #
    cmpt
    #
    vy
    @9
    @3
    ctopn
    cfv
    #
    vx
    vy
    @1
    @8
    vy
    cv
    #
    cc0
    wceq
    #
    cpnf
    @11
    clog
    cfv
    #
    cneg
    #
    cif
    @4
    @11
    wceq
    #
    @5
    @12
    @7
    @14
    cpnf
    @4
    @11
    cc0
    eqeq1
    @15
    @6
    @13
    @4
    @11
    clog
    fveq2
    negeqd
    ifbieq2d
    cbvmptv
    #
    xrge0topn
    xrge0iifmhm
    @9
    cii
    @10
    chmeo
    co
    @2
    ctopn
    cfv
    #
    @10
    chmeo
    co
    vy
    @9
    @10
    @16
    xrge0topn
    xrge0iifhmeo
    cii
    @17
    @10
    chmeo
    ccnfld
    @1
    cress
    co
    #
    cii
    @2
    ccnfld
    cvv
    wcel
    @1
    cvv
    wcel
    @2
    @18
    cmgp
    cfv
    wceq
    cnfldex
    cc0
    c1
    cicc
    ovex
    @1
    ccnfld
    @18
    @0
    cvv
    cvv
    @18
    eqid
    #
    @0
    eqid
    mgpress
    mp2an
    @18
    @19
    dfii4
    mgptopn
    oveq1i
    eleqtri
    @2
    @2
    eqid
    iistmd
    xrge0tps
    mhmhmeotmd
end
