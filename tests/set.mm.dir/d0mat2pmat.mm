include "wcel.mm"
include "c0.mm"
include "cmat2pmat.mm"
include "co.mm"
include "cfv.mm"
include "cv.mm"
include "cpl1.mm"
include "cascl.mm"
include "cmpt2.mm"
include "cfn.mm"
include "cmat.mm"
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
include "mat2pmatval.mm"
include "syl3anc.mm"
include "mpt20.mm"
include "syl6eq.mm"

theorem d0mat2pmat
  let cR: class R
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( R e. V -> ( ( (/) matToPolyMat R ) ` (/) ) = (/) )

  proof
    cR
    cV
    wcel
    #
    c0
    c0
    cR
    cmat2pmat
    co
    #
    cfv
    #
    vx
    vy
    c0
    c0
    vx
    cv
    vy
    cv
    c0
    co
    cR
    cpl1
    cfv
    #
    cascl
    cfv
    #
    cfv
    #
    cmpt2
    #
    c0
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
    @2
    @6
    wceq
    @7
    @0
    0fin
    a1i
    @0
    id
    @0
    c0
    c0
    csn
    @9
    c0
    0ex
    snid
    cR
    cV
    mat0dimbas0
    syl5eleqr
    vx
    vy
    @8
    @9
    @3
    cR
    @4
    @1
    c0
    c0
    cV
    @1
    eqid
    @8
    eqid
    @9
    eqid
    @3
    eqid
    @4
    eqid
    mat2pmatval
    syl3anc
    vx
    vy
    c0
    @5
    mpt20
    syl6eq
end
