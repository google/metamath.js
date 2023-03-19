include "crg.mm"
include "wcel.mm"
include "c0.mm"
include "cscmat.mm"
include "co.mm"
include "cmat.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cur.mm"
include "cvsca.mm"
include "wceq.mm"
include "wrex.mm"
include "csn.mm"
include "0ex.mm"
include "snid.mm"
include "mat0dimbas0.mm"
include "syl5eleqr.mm"
include "eqid.mm"
include "ringidcl.mm"
include "wb.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "mat0dimscm.mm"
include "mpdan.mm"
include "eqcomd.mm"
include "rspcedvd.mm"
include "mat0dimid.mm"
include "oveq2d.mm"
include "rexbidv.mm"
include "mpbird.mm"
include "cfn.mm"
include "wa.mm"
include "0fin.mm"
include "scmatel.mm"
include "mpan.mm"
include "mpbir2and.mm"

theorem mat0scmat
  let cR: class R
  let vc: setvar c


  assert |- ( R e. Ring -> (/) e. ( (/) ScMat R ) )

  proof
    cR
    crg
    wcel
    #
    c0
    c0
    cR
    cscmat
    co
    #
    wcel
    #
    c0
    c0
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    wcel
    #
    c0
    vc
    cv
    #
    @3
    cur
    cfv
    #
    @3
    cvsca
    cfv
    #
    co
    #
    wceq
    #
    vc
    cR
    cbs
    cfv
    #
    wrex
    #
    @0
    c0
    c0
    csn
    @4
    c0
    0ex
    snid
    cR
    crg
    mat0dimbas0
    syl5eleqr
    @0
    @12
    c0
    @6
    c0
    @8
    co
    #
    wceq
    #
    vc
    @11
    wrex
    @0
    @14
    c0
    cR
    cur
    cfv
    #
    c0
    @8
    co
    #
    wceq
    #
    vc
    @15
    @11
    @11
    cR
    @15
    @11
    eqid
    #
    @15
    eqid
    ringidcl
    #
    @6
    @15
    wceq
    #
    @14
    @17
    wb
    @0
    @20
    @13
    @16
    c0
    @6
    @15
    c0
    @8
    oveq1
    eqeq2d
    adantl
    @0
    @16
    c0
    @0
    @15
    @11
    wcel
    @16
    c0
    wceq
    @19
    @3
    cR
    @15
    @3
    eqid
    #
    mat0dimscm
    mpdan
    eqcomd
    rspcedvd
    @0
    @10
    @14
    vc
    @11
    @0
    @9
    @13
    c0
    @0
    @7
    c0
    @6
    @8
    @3
    cR
    @21
    mat0dimid
    oveq2d
    eqeq2d
    rexbidv
    mpbird
    c0
    cfn
    wcel
    @0
    @2
    @5
    @12
    wa
    wb
    0fin
    @3
    @4
    cR
    @1
    @8
    @7
    @11
    c0
    c0
    crg
    vc
    @18
    @21
    @4
    eqid
    @7
    eqid
    @8
    eqid
    @1
    eqid
    scmatel
    mpan
    mpbir2and
end
