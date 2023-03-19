include "crg.mm"
include "wcel.mm"
include "c0.mm"
include "cfv.mm"
include "cv1.mm"
include "cpl1.mm"
include "cmat.mm"
include "co.mm"
include "cur.mm"
include "cvsca.mm"
include "cmat2pmat.mm"
include "csg.mm"
include "cmdat.mm"
include "cfn.mm"
include "cbs.mm"
include "wceq.mm"
include "0fin.mm"
include "a1i.mm"
include "id.mm"
include "csn.mm"
include "0ex.mm"
include "snid.mm"
include "mat0dimbas0.mm"
include "syl5eleqr.mm"
include "eqid.mm"
include "chpmatval.mm"
include "syl3anc.mm"
include "cop.mm"
include "ply1ring.mm"
include "mdet0pr.mm"
include "fveq1d.mm"
include "syl.mm"
include "c0g.mm"
include "mat0dimid.mm"
include "oveq2d.mm"
include "vr1cl.mm"
include "mat0dimscm.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "d0mat2pmat.mm"
include "oveq12d.mm"
include "cgrp.mm"
include "matring.mm"
include "sylancr.mm"
include "ringgrp.mm"
include "grpsubid.mm"
include "fveq2d.mm"
include "mat0dim0.mm"
include "fvex.mm"
include "fvsn.mm"
include "syl6eq.mm"

theorem chpmat0d
  let cC: class C
  let cR: class R
  assume chpmat0.c: |- C = ( (/) CharPlyMat R )


  assert |- ( R e. Ring -> ( C ` (/) ) = ( 1r ` ( Poly1 ` R ) ) )

  proof
    cR
    crg
    wcel
    #
    c0
    cC
    cfv
    #
    cR
    cv1
    cfv
    #
    c0
    cR
    cpl1
    cfv
    #
    cmat
    co
    #
    cur
    cfv
    #
    @4
    cvsca
    cfv
    #
    co
    #
    c0
    c0
    cR
    cmat2pmat
    co
    #
    cfv
    #
    @4
    csg
    cfv
    #
    co
    #
    c0
    @3
    cmdat
    co
    #
    cfv
    #
    @3
    cur
    cfv
    #
    @0
    c0
    cfn
    wcel
    #
    @0
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
    @1
    @13
    wceq
    @15
    @0
    0fin
    a1i
    @0
    id
    @0
    c0
    c0
    csn
    #
    @17
    c0
    0ex
    snid
    #
    cR
    crg
    mat0dimbas0
    syl5eleqr
    @16
    @17
    cC
    @12
    @3
    cR
    @8
    @6
    @5
    c0
    @10
    c0
    crg
    @2
    @4
    chpmat0.c
    @16
    eqid
    @17
    eqid
    @3
    eqid
    #
    @4
    eqid
    #
    @12
    eqid
    @10
    eqid
    #
    @2
    eqid
    #
    @6
    eqid
    @8
    eqid
    @5
    eqid
    chpmatval
    syl3anc
    @0
    @13
    @11
    c0
    @14
    cop
    csn
    #
    cfv
    #
    @14
    @0
    @3
    crg
    wcel
    #
    @13
    @25
    wceq
    @3
    cR
    @20
    ply1ring
    #
    @26
    @11
    @12
    @24
    @3
    mdet0pr
    fveq1d
    syl
    @0
    @25
    @4
    c0g
    cfv
    #
    @24
    cfv
    #
    @14
    @0
    @11
    @28
    @24
    @0
    @11
    c0
    c0
    @10
    co
    #
    @28
    @0
    @7
    c0
    @9
    c0
    @10
    @0
    @7
    @2
    c0
    @6
    co
    #
    c0
    @0
    @5
    c0
    @2
    @6
    @0
    @26
    @5
    c0
    wceq
    @27
    @4
    @3
    @21
    mat0dimid
    syl
    oveq2d
    @0
    @26
    @2
    @3
    cbs
    cfv
    #
    wcel
    @31
    c0
    wceq
    @27
    @32
    @3
    cR
    @2
    @23
    @20
    @32
    eqid
    vr1cl
    @4
    @3
    @2
    @21
    mat0dimscm
    syl2anc
    eqtrd
    cR
    crg
    d0mat2pmat
    oveq12d
    @0
    @4
    cgrp
    wcel
    #
    c0
    @4
    cbs
    cfv
    #
    wcel
    @30
    @28
    wceq
    @0
    @4
    crg
    wcel
    #
    @33
    @0
    @15
    @26
    @35
    0fin
    @27
    @4
    @3
    c0
    @21
    matring
    sylancr
    @4
    ringgrp
    syl
    @0
    c0
    @18
    @34
    @19
    @0
    @26
    @34
    @18
    wceq
    @27
    @3
    crg
    mat0dimbas0
    syl
    syl5eleqr
    @34
    @4
    @10
    c0
    @28
    @34
    eqid
    @28
    eqid
    @22
    grpsubid
    syl2anc
    eqtrd
    fveq2d
    @0
    @29
    c0
    @24
    cfv
    @14
    @0
    @28
    c0
    @24
    @0
    @26
    @28
    c0
    wceq
    @27
    @4
    @3
    @21
    mat0dim0
    syl
    fveq2d
    c0
    @14
    0ex
    @3
    cur
    fvex
    fvsn
    syl6eq
    eqtrd
    eqtrd
    eqtrd
end
