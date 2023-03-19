include "cc.mm"
include "c1.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cima.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "wcel.mm"
include "crab.mm"
include "eqid.mm"
include "mptpreima.mm"
include "eqtr4i.mm"
include "ccn.mm"
include "wtru.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "1cnd.mm"
include "cnmptc.mm"
include "cn0.mm"
include "2nn0.mm"
include "expcn.mm"
include "mp1i.mm"
include "ctx.mm"
include "addcn.mm"
include "cnmpt12f.mm"
include "trud.mm"
include "logdmopn.mm"
include "cnima.mm"
include "mp2an.mm"
include "eqeltri.mm"

theorem atansopn
  let vy: setvar y
  let cD: class D
  let cS: class S
  let cA: class A
  let vx: setvar x
  assume atansopn.d: |- D = ( CC \ ( -oo (,] 0 ) )
  assume atansopn.s: |- S = { y e. CC | ( 1 + ( y ^ 2 ) ) e. D }

  disjoint D y
  disjoint A y
  disjoint x y
  disjoint D x
  disjoint S x
  assert |- S e. ( TopOpen ` CCfld )

  proof
    cS
    vy
    cc
    c1
    vy
    cv
    c2
    cexp
    co
    #
    caddc
    co
    #
    cmpt
    #
    ccnv
    cD
    cima
    #
    ccnfld
    ctopn
    cfv
    #
    cS
    @1
    cD
    wcel
    vy
    cc
    crab
    @3
    atansopn.s
    vy
    cc
    @1
    cD
    @2
    @2
    eqid
    mptpreima
    eqtr4i
    @2
    @4
    @4
    ccn
    co
    #
    wcel
    #
    cD
    @4
    wcel
    @3
    @4
    wcel
    @6
    wtru
    vy
    c1
    @0
    caddc
    @4
    @4
    @4
    @4
    cc
    @4
    cc
    ctopon
    cfv
    wcel
    wtru
    @4
    @4
    eqid
    #
    cnfldtopon
    a1i
    #
    wtru
    vy
    c1
    @4
    @4
    cc
    cc
    @8
    @8
    wtru
    1cnd
    cnmptc
    c2
    cn0
    wcel
    vy
    cc
    @0
    cmpt
    @5
    wcel
    wtru
    2nn0
    vy
    @4
    c2
    @7
    expcn
    mp1i
    caddc
    @4
    @4
    ctx
    co
    @4
    ccn
    co
    wcel
    wtru
    @4
    @7
    addcn
    a1i
    cnmpt12f
    trud
    cD
    atansopn.d
    logdmopn
    cD
    @2
    @4
    @4
    cnima
    mp2an
    eqeltri
end
