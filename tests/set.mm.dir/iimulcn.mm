include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "cmul.mm"
include "cmpt2.mm"
include "cii.mm"
include "ctx.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "ccn.mm"
include "wcel.mm"
include "wtru.mm"
include "cc.mm"
include "eqid.mm"
include "dfii3.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "wss.mm"
include "cr.mm"
include "unitssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "cxp.mm"
include "wfn.mm"
include "wceq.mm"
include "wf.mm"
include "ax-mulf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "fnov.mm"
include "mpbi.mm"
include "mulcn.mm"
include "eqeltrri.mm"
include "cnmpt2res.mm"
include "trud.mm"
include "crn.mm"
include "wb.mm"
include "wral.mm"
include "iimulcl.mm"
include "rgen2a.mm"
include "fmpt2.mm"
include "frn.mm"
include "sylbi.mm"
include "cnrest2.mm"
include "mp3an.mm"
include "oveq2i.mm"
include "eleqtrri.mm"

theorem iimulcn
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( x e. ( 0 [,] 1 ) , y e. ( 0 [,] 1 ) |-> ( x x. y ) ) e. ( ( II tX II ) Cn II )

  proof
    vx
    vy
    cc0
    c1
    cicc
    co
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    cmul
    co
    #
    cmpt2
    #
    cii
    cii
    ctx
    co
    #
    ccnfld
    ctopn
    cfv
    #
    @0
    crest
    co
    #
    ccn
    co
    #
    @5
    cii
    ccn
    co
    @4
    @5
    @6
    ccn
    co
    wcel
    #
    @4
    @8
    wcel
    #
    @9
    wtru
    vx
    vy
    @3
    @6
    cii
    @6
    @6
    cii
    @0
    cc
    @0
    cc
    @6
    @6
    eqid
    #
    dfii3
    #
    @6
    cc
    ctopon
    cfv
    wcel
    #
    wtru
    @6
    @11
    cnfldtopon
    #
    a1i
    #
    @0
    cc
    wss
    #
    wtru
    @0
    cr
    cc
    unitssre
    ax-resscn
    sstri
    #
    a1i
    #
    @12
    @15
    @18
    vx
    vy
    cc
    cc
    @3
    cmpt2
    #
    @6
    @6
    ctx
    co
    @6
    ccn
    co
    #
    wcel
    wtru
    cmul
    @19
    @20
    cmul
    cc
    cc
    cxp
    #
    wfn
    #
    cmul
    @19
    wceq
    @21
    cc
    cmul
    wf
    @22
    ax-mulf
    @21
    cc
    cmul
    ffn
    ax-mp
    vx
    vy
    cc
    cc
    cmul
    fnov
    mpbi
    @6
    @11
    mulcn
    eqeltrri
    a1i
    cnmpt2res
    trud
    @13
    @4
    crn
    @0
    wss
    #
    @16
    @9
    @10
    wb
    @14
    @3
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
    @23
    @24
    vx
    vy
    @0
    @1
    @2
    iimulcl
    rgen2a
    @25
    @0
    @0
    cxp
    #
    @0
    @4
    wf
    @23
    vx
    vy
    @0
    @0
    @3
    @0
    @4
    @4
    eqid
    fmpt2
    @26
    @0
    @4
    frn
    sylbi
    ax-mp
    @17
    @0
    @4
    @5
    @6
    cc
    cnrest2
    mp3an
    mpbi
    cii
    @7
    @5
    ccn
    @12
    oveq2i
    eleqtrri
end
