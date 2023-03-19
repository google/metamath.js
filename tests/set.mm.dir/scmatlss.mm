include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "clss.mm"
include "cvsca.mm"
include "matsca2.mm"
include "eqidd.mm"
include "cv.mm"
include "cur.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "crab.mm"
include "eqid.mm"
include "scmatval.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "c0.mm"
include "wne.mm"
include "c0g.mm"
include "scmatid.mm"
include "ne0i.mm"
include "syl.mm"
include "w3a.mm"
include "smatvscl.mm"
include "3adantr3.mm"
include "simpr3.mm"
include "jca.mm"
include "scmataddcl.mm"
include "syldan.mm"
include "islssd.mm"

theorem scmatlss
  let cA: class A
  let cR: class R
  let cS: class S
  let cN: class N
  let va: setvar a
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let vc: setvar c
  assume scmatlss.a: |- A = ( N Mat R )
  assume scmatlss.s: |- S = ( N ScMat R )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> S e. ( LSubSp ` A ) )

  proof
    cN
    cfn
    wcel
    cR
    crg
    wcel
    wa
    #
    va
    cR
    cbs
    cfv
    #
    cA
    cplusg
    cfv
    #
    cA
    clss
    cfv
    #
    cA
    cvsca
    cfv
    #
    cS
    cR
    cA
    cbs
    cfv
    #
    cA
    vx
    vy
    cA
    cR
    cN
    crg
    scmatlss.a
    matsca2
    @0
    @1
    eqidd
    @0
    @5
    eqidd
    @0
    @2
    eqidd
    @0
    @4
    eqidd
    @0
    @3
    eqidd
    @0
    cS
    vm
    cv
    vc
    cv
    cA
    cur
    cfv
    #
    @4
    co
    wceq
    vc
    @1
    wrex
    #
    vm
    @5
    crab
    @5
    cA
    @5
    cR
    cS
    @4
    @6
    vm
    @1
    cN
    crg
    vc
    @1
    eqid
    #
    scmatlss.a
    @5
    eqid
    #
    @6
    eqid
    @4
    eqid
    #
    scmatlss.s
    scmatval
    @7
    vm
    @5
    ssrab2
    syl6eqss
    @0
    @6
    cS
    wcel
    cS
    c0
    wne
    cA
    @5
    cR
    cS
    @1
    cN
    cR
    c0g
    cfv
    #
    scmatlss.a
    @9
    @8
    @11
    eqid
    #
    scmatlss.s
    scmatid
    cS
    @6
    ne0i
    syl
    @0
    va
    cv
    #
    @1
    wcel
    #
    vx
    cv
    #
    cS
    wcel
    #
    vy
    cv
    #
    cS
    wcel
    #
    w3a
    #
    @13
    @15
    @4
    co
    #
    cS
    wcel
    #
    @18
    wa
    @20
    @17
    @2
    co
    cS
    wcel
    @0
    @19
    wa
    @21
    @18
    @0
    @14
    @16
    @21
    @18
    cA
    @13
    cR
    cS
    @4
    @1
    cN
    @15
    @8
    scmatlss.a
    scmatlss.s
    @10
    smatvscl
    3adantr3
    @0
    @14
    @16
    @18
    simpr3
    jca
    cA
    @5
    cR
    cS
    @1
    cN
    @20
    @17
    @11
    scmatlss.a
    @9
    @8
    @12
    scmatlss.s
    scmataddcl
    syldan
    islssd
end
