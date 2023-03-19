include "wcel.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "cn0.mm"
include "cv.mm"
include "cmg.mm"
include "cfv.mm"
include "co.mm"
include "c0g.mm"
include "wral.mm"
include "crab.mm"
include "c0.mm"
include "wa.mm"
include "eqid.mm"
include "gexlem1.mm"
include "simpl.mm"
include "elrabi.mm"
include "orim12i.mm"
include "syl.mm"
include "orcomd.mm"
include "elnn0.mm"
include "sylibr.mm"

theorem gexcl
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  let c.0: class .0.
  let c.x: class .x.
  assume gexcl.1: |- X = ( Base ` G )
  assume gexcl.2: |- E = ( gEx ` G )


  assert |- ( G e. V -> E e. NN0 )

  proof
    cG
    cV
    wcel
    #
    cE
    cn
    wcel
    #
    cE
    cc0
    wceq
    #
    wo
    cE
    cn0
    wcel
    @0
    @2
    @1
    @0
    @2
    vy
    cv
    vx
    cv
    cG
    cmg
    cfv
    #
    co
    cG
    c0g
    cfv
    #
    wceq
    vx
    cX
    wral
    #
    vy
    cn
    crab
    #
    c0
    wceq
    #
    wa
    #
    cE
    @6
    wcel
    #
    wo
    @2
    @1
    wo
    vx
    vy
    @3
    cE
    cG
    @6
    cV
    cX
    @4
    gexcl.1
    @3
    eqid
    @4
    eqid
    gexcl.2
    @6
    eqid
    gexlem1
    @8
    @2
    @9
    @1
    @2
    @7
    simpl
    @5
    vy
    cE
    cn
    elrabi
    orim12i
    syl
    orcomd
    cE
    elnn0
    sylibr
end
