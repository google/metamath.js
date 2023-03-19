include "wcel.mm"
include "cfv.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "cn0.mm"
include "cv.mm"
include "cmg.mm"
include "co.mm"
include "c0g.mm"
include "crab.mm"
include "c0.mm"
include "wa.mm"
include "eqid.mm"
include "odlem1.mm"
include "simpl.mm"
include "elrabi.mm"
include "orim12i.mm"
include "syl.mm"
include "orcomd.mm"
include "elnn0.mm"
include "sylibr.mm"

theorem odcl
  let cA: class A
  let cG: class G
  let cO: class O
  let cX: class X
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let c.0: class .0.
  let vx: setvar x
  let cN: class N
  let c.x: class .x.
  assume odcl.1: |- X = ( Base ` G )
  assume odcl.2: |- O = ( od ` G )


  assert |- ( A e. X -> ( O ` A ) e. NN0 )

  proof
    cA
    cX
    wcel
    #
    cA
    cO
    cfv
    #
    cn
    wcel
    #
    @1
    cc0
    wceq
    #
    wo
    @1
    cn0
    wcel
    @0
    @3
    @2
    @0
    @3
    vy
    cv
    cA
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
    @1
    @7
    wcel
    #
    wo
    @3
    @2
    wo
    vy
    cA
    @4
    cG
    @7
    cO
    cX
    @5
    odcl.1
    @4
    eqid
    @5
    eqid
    odcl.2
    @7
    eqid
    odlem1
    @9
    @3
    @10
    @2
    @3
    @8
    simpl
    @6
    vy
    @1
    cn
    elrabi
    orim12i
    syl
    orcomd
    @1
    elnn0
    sylibr
end
