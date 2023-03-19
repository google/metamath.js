include "caddc.mm"
include "cr.mm"
include "cxp.mm"
include "cres.mm"
include "ctx.mm"
include "co.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "ccn.mm"
include "cv.mm"
include "cmpt2.mm"
include "wcel.mm"
include "cc.mm"
include "wss.mm"
include "eqid.mm"
include "addcn.mm"
include "ax-resscn.mm"
include "xpss12.mm"
include "mp2an.mm"
include "cnfldtop.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "txunii.mm"
include "cnrest.mm"
include "ctop.mm"
include "cvv.mm"
include "wceq.mm"
include "reex.mm"
include "txrest.mm"
include "mp4an.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "tgioo2.mm"
include "eqtr2i.mm"
include "oveq12i.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "eleqtri.mm"
include "ctopon.mm"
include "wb.mm"
include "wfn.mm"
include "wf.mm"
include "ax-addf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "fnssres.mm"
include "fnov.mm"
include "mpbi.mm"
include "ovres.mm"
include "mpt2eq3ia.mm"
include "rneqi.mm"
include "wral.mm"
include "readdcl.mm"
include "rgen2a.mm"
include "rnmpt2ss.mm"
include "eqsstri.mm"
include "cnrest2.mm"
include "mp3an.mm"
include "oveq2i.mm"
include "3eltr3i.mm"

theorem raddcn
  let vx: setvar x
  let vy: setvar y
  let cJ: class J
  assume raddcn.1: |- J = ( topGen ` ran (,) )

  disjoint x y
  assert |- ( x e. RR , y e. RR |-> ( x + y ) ) e. ( ( J tX J ) Cn J )

  proof
    caddc
    cr
    cr
    cxp
    #
    cres
    #
    cJ
    cJ
    ctx
    co
    #
    ccnfld
    ctopn
    cfv
    #
    cr
    crest
    co
    #
    ccn
    co
    #
    vx
    vy
    cr
    cr
    vx
    cv
    #
    vy
    cv
    #
    caddc
    co
    #
    cmpt2
    #
    @2
    cJ
    ccn
    co
    @1
    @2
    @3
    ccn
    co
    #
    wcel
    #
    @1
    @5
    wcel
    #
    @1
    @3
    @3
    ctx
    co
    #
    @0
    crest
    co
    #
    @3
    ccn
    co
    #
    @10
    caddc
    @13
    @3
    ccn
    co
    wcel
    @0
    cc
    cc
    cxp
    #
    wss
    #
    @1
    @15
    wcel
    @3
    @3
    eqid
    #
    addcn
    cr
    cc
    wss
    #
    @19
    @17
    ax-resscn
    ax-resscn
    cr
    cc
    cr
    cc
    xpss12
    mp2an
    #
    @0
    caddc
    @13
    @3
    @16
    @3
    @3
    cc
    cc
    @3
    @18
    cnfldtop
    #
    @21
    cc
    @3
    @3
    @18
    cnfldtopon
    #
    toponunii
    #
    @23
    txunii
    cnrest
    mp2an
    @14
    @2
    @3
    ccn
    @14
    @4
    @4
    ctx
    co
    #
    @2
    @3
    ctop
    wcel
    #
    @25
    cr
    cvv
    wcel
    #
    @26
    @14
    @24
    wceq
    @21
    @21
    reex
    reex
    cr
    cr
    @3
    @3
    ctop
    ctop
    cvv
    cvv
    txrest
    mp4an
    @4
    cJ
    @4
    cJ
    ctx
    cJ
    cioo
    crn
    ctg
    cfv
    @4
    raddcn.1
    @3
    @18
    tgioo2
    eqtr2i
    #
    @27
    oveq12i
    eqtri
    oveq1i
    eleqtri
    @3
    cc
    ctopon
    cfv
    wcel
    @1
    crn
    #
    cr
    wss
    @19
    @11
    @12
    wb
    @22
    @28
    @9
    crn
    #
    cr
    @1
    @9
    @1
    vx
    vy
    cr
    cr
    @6
    @7
    @1
    co
    #
    cmpt2
    #
    @9
    @1
    @0
    wfn
    #
    @1
    @31
    wceq
    caddc
    @16
    wfn
    #
    @17
    @32
    @16
    cc
    caddc
    wf
    @33
    ax-addf
    @16
    cc
    caddc
    ffn
    ax-mp
    @20
    @16
    @0
    caddc
    fnssres
    mp2an
    vx
    vy
    cr
    cr
    @1
    fnov
    mpbi
    vx
    vy
    cr
    cr
    @30
    @8
    @6
    @7
    cr
    cr
    caddc
    ovres
    mpt2eq3ia
    eqtri
    #
    rneqi
    @8
    cr
    wcel
    #
    vy
    cr
    wral
    vx
    cr
    wral
    @29
    cr
    wss
    @35
    vx
    vy
    cr
    @6
    @7
    readdcl
    rgen2a
    vx
    vy
    cr
    cr
    @8
    cr
    @9
    @9
    eqid
    rnmpt2ss
    ax-mp
    eqsstri
    ax-resscn
    cr
    @1
    @2
    @3
    cc
    cnrest2
    mp3an
    mpbi
    @34
    @4
    cJ
    @2
    ccn
    @27
    oveq2i
    3eltr3i
end
