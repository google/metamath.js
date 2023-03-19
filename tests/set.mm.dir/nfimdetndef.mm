include "cfn.mm"
include "wnel.mm"
include "cmat.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "csymg.mm"
include "cv.mm"
include "czrh.mm"
include "cpsgn.mm"
include "ccom.mm"
include "cmgp.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmulr.mm"
include "c0.mm"
include "eqid.mm"
include "mdetfval.mm"
include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "wn.mm"
include "wceq.mm"
include "df-nel.mm"
include "biimpi.mm"
include "intnanrd.mm"
include "matbas0.mm"
include "syl.mm"
include "mpteq1d.mm"
include "mpt0.mm"
include "syl6eq.mm"
include "syl5eq.mm"

theorem nfimdetndef
  let cD: class D
  let cR: class R
  let cN: class N
  let vm: setvar m
  let vp: setvar p
  let vx: setvar x
  assume nfimdetndef.d: |- D = ( N maDet R )


  assert |- ( N e/ Fin -> D = (/) )

  proof
    cN
    cfn
    wnel
    #
    cD
    vm
    cN
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    cR
    vp
    cN
    csymg
    cfv
    cbs
    cfv
    #
    vp
    cv
    #
    cR
    czrh
    cfv
    #
    cN
    cpsgn
    cfv
    #
    ccom
    cfv
    cR
    cmgp
    cfv
    #
    vx
    cN
    vx
    cv
    #
    @4
    cfv
    @8
    vm
    cv
    co
    cmpt
    cgsu
    co
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
    vx
    @1
    @2
    cD
    @3
    cR
    @6
    @9
    @7
    vm
    cN
    @5
    vp
    nfimdetndef.d
    @1
    eqid
    @2
    eqid
    @3
    eqid
    @5
    eqid
    @6
    eqid
    @9
    eqid
    @7
    eqid
    mdetfval
    @0
    @11
    vm
    c0
    @10
    cmpt
    c0
    @0
    vm
    @2
    c0
    @10
    @0
    cN
    cfn
    wcel
    #
    cR
    cvv
    wcel
    #
    wa
    wn
    @2
    c0
    wceq
    @0
    @12
    @13
    @0
    @12
    wn
    cN
    cfn
    df-nel
    biimpi
    intnanrd
    cR
    cN
    matbas0
    syl
    mpteq1d
    vm
    @10
    mpt0
    syl6eq
    syl5eq
end
