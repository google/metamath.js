include "c0.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmulr.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmat.mm"
include "cbs.mm"
include "eqid.mm"
include "simpr.mm"
include "cfn.mm"
include "0fin.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "adantr.mm"
include "csn.mm"
include "cvv.mm"
include "0ex.mm"
include "snidg.mm"
include "mp1i.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "mat0dimbas0.mm"
include "adantl.mm"
include "eqtrd.mm"
include "eleqtrrd.mm"
include "cmap.mm"
include "c1o.mm"
include "eqidd.mm"
include "el1o.mm"
include "sylibr.mm"
include "oveq2.mm"
include "fvex.mm"
include "map0e.mm"
include "mavmulval.mm"
include "mpteq1.mm"
include "mpt0.mm"
include "syl6eq.mm"

theorem mavmul0
  let cR: class R
  let c.x: class .x.
  let cN: class N
  let cV: class V
  let vi: setvar i
  let vj: setvar j
  assume mavmul0.t: |- .x. = ( R maVecMul <. N , N >. )


  assert |- ( ( N = (/) /\ R e. V ) -> ( (/) .x. (/) ) = (/) )

  proof
    cN
    c0
    wceq
    #
    cR
    cV
    wcel
    #
    wa
    #
    c0
    c0
    c.x
    co
    vi
    cN
    cR
    vj
    cN
    vi
    cv
    vj
    cv
    #
    c0
    co
    @3
    c0
    cfv
    cR
    cmulr
    cfv
    #
    co
    cmpt
    cgsu
    co
    #
    cmpt
    #
    c0
    @2
    cN
    cR
    cmat
    co
    #
    cR
    cbs
    cfv
    #
    cR
    @4
    c.x
    vi
    vj
    cN
    cV
    c0
    c0
    @7
    eqid
    mavmul0.t
    @8
    eqid
    @4
    eqid
    @0
    @1
    simpr
    @0
    cN
    cfn
    wcel
    #
    @1
    @0
    @9
    c0
    cfn
    wcel
    0fin
    cN
    c0
    cfn
    eleq1
    mpbiri
    adantr
    @2
    c0
    c0
    csn
    #
    @7
    cbs
    cfv
    #
    c0
    cvv
    wcel
    c0
    @10
    wcel
    @2
    0ex
    c0
    cvv
    snidg
    mp1i
    @2
    @11
    c0
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    @10
    @2
    @7
    @12
    cbs
    @0
    @7
    @12
    wceq
    @1
    cN
    c0
    cR
    cmat
    oveq1
    adantr
    fveq2d
    @1
    @13
    @10
    wceq
    @0
    cR
    cV
    mat0dimbas0
    adantl
    eqtrd
    eleqtrrd
    @0
    c0
    @8
    cN
    cmap
    co
    #
    wcel
    @1
    @0
    c0
    c1o
    @14
    @0
    c0
    c0
    wceq
    c0
    c1o
    wcel
    @0
    c0
    eqidd
    c0
    el1o
    sylibr
    @0
    @14
    @8
    c0
    cmap
    co
    #
    c1o
    cN
    c0
    @8
    cmap
    oveq2
    @8
    cvv
    wcel
    @15
    c1o
    wceq
    @0
    cR
    cbs
    fvex
    @8
    cvv
    map0e
    mp1i
    eqtrd
    eleqtrrd
    adantr
    mavmulval
    @2
    @6
    vi
    c0
    @5
    cmpt
    #
    c0
    @0
    @6
    @16
    wceq
    @1
    vi
    cN
    c0
    @5
    mpteq1
    adantr
    vi
    @5
    mpt0
    syl6eq
    eqtrd
end
