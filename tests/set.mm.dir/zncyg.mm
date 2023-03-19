include "cn0.mm"
include "wcel.mm"
include "cgrp.mm"
include "cz.mm"
include "cv.mm"
include "cmg.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "cbs.mm"
include "wceq.mm"
include "wrex.mm"
include "ccyg.mm"
include "crg.mm"
include "ccrg.mm"
include "zncrng.mm"
include "crngring.mm"
include "syl.mm"
include "ringgrp.mm"
include "cur.mm"
include "eqid.mm"
include "ringidcl.mm"
include "czrh.mm"
include "zrhval2.mm"
include "rneqd.mm"
include "wfo.mm"
include "znzrhfo.mm"
include "forn.mm"
include "eqtr3d.mm"
include "oveq2.mm"
include "mpteq2dv.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "iscyg.mm"
include "sylanbrc.mm"

theorem zncyg
  let cN: class N
  let cY: class Y
  let cA: class A
  let vx: setvar x
  let cB: class B
  let vn: setvar n
  assume zncyg.y: |- Y = ( Z/nZ ` N )


  assert |- ( N e. NN0 -> Y e. CycGrp )

  proof
    cN
    cn0
    wcel
    #
    cY
    cgrp
    wcel
    #
    vn
    cz
    vn
    cv
    #
    vx
    cv
    #
    cY
    cmg
    cfv
    #
    co
    #
    cmpt
    #
    crn
    #
    cY
    cbs
    cfv
    #
    wceq
    #
    vx
    @8
    wrex
    #
    cY
    ccyg
    wcel
    @0
    cY
    crg
    wcel
    #
    @1
    @0
    cY
    ccrg
    wcel
    @11
    cN
    cY
    zncyg.y
    zncrng
    cY
    crngring
    syl
    #
    cY
    ringgrp
    syl
    @0
    cY
    cur
    cfv
    #
    @8
    wcel
    #
    vn
    cz
    @2
    @13
    @4
    co
    #
    cmpt
    #
    crn
    #
    @8
    wceq
    #
    @10
    @0
    @11
    @14
    @12
    @8
    cY
    @13
    @8
    eqid
    #
    @13
    eqid
    #
    ringidcl
    syl
    @0
    cY
    czrh
    cfv
    #
    crn
    #
    @17
    @8
    @0
    @21
    @16
    @0
    @11
    @21
    @16
    wceq
    @12
    cY
    @4
    @13
    vn
    @21
    @21
    eqid
    #
    @4
    eqid
    #
    @20
    zrhval2
    syl
    rneqd
    @0
    cz
    @8
    @21
    wfo
    @22
    @8
    wceq
    @8
    @21
    cN
    cY
    zncyg.y
    @19
    @23
    znzrhfo
    cz
    @8
    @21
    forn
    syl
    eqtr3d
    @9
    @18
    vx
    @13
    @8
    @3
    @13
    wceq
    #
    @7
    @17
    @8
    @25
    @6
    @16
    @25
    vn
    cz
    @5
    @15
    @3
    @13
    @2
    @4
    oveq2
    mpteq2dv
    rneqd
    eqeq1d
    rspcev
    syl2anc
    vx
    @8
    @4
    vn
    cY
    @19
    @24
    iscyg
    sylanbrc
end
