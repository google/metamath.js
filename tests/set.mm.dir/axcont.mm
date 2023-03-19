include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "w3a.mm"
include "simpr.mm"
include "3anim3i.mm"
include "anim2i.mm"
include "simpr3l.mm"
include "axcontlem12.mm"
include "syl2anc.mm"
include "3exp2.mm"
include "com4r.mm"
include "rexlimiva.mm"
include "com4l.mm"
include "3imp2.mm"

theorem axcont
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cN: class N
  let va: setvar a
  let vb: setvar b

  disjoint A a
  disjoint A b
  disjoint A x
  disjoint A y
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint x y
  disjoint B a
  disjoint B b
  disjoint B x
  disjoint B y
  disjoint N a
  disjoint N b
  disjoint N x
  disjoint N y
  assert |- ( ( N e. NN /\ ( A C_ ( EE ` N ) /\ B C_ ( EE ` N ) /\ E. a e. ( EE ` N ) A. x e. A A. y e. B x Btwn <. a , y >. ) ) -> E. b e. ( EE ` N ) A. x e. A A. y e. B b Btwn <. x , y >. )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wss
    #
    cB
    @1
    wss
    #
    vx
    cv
    #
    va
    cv
    #
    vy
    cv
    #
    cop
    cbtwn
    wbr
    vy
    cB
    wral
    vx
    cA
    wral
    #
    va
    @1
    wrex
    #
    vb
    cv
    @4
    @6
    cop
    cbtwn
    wbr
    vy
    cB
    wral
    vx
    cA
    wral
    vb
    @1
    wrex
    #
    @8
    @0
    @2
    @3
    @9
    @7
    @0
    @2
    @3
    @9
    wi
    wi
    wi
    va
    @1
    @0
    @2
    @3
    @5
    @1
    wcel
    #
    @7
    wa
    #
    @9
    @0
    @2
    @3
    @11
    @9
    @0
    @2
    @3
    @11
    w3a
    #
    wa
    @0
    @2
    @3
    @7
    w3a
    #
    wa
    @10
    @9
    @12
    @13
    @0
    @11
    @7
    @2
    @3
    @10
    @7
    simpr
    3anim3i
    anim2i
    @10
    @7
    @2
    @3
    @0
    simpr3l
    vx
    vy
    cA
    cB
    cN
    @5
    vb
    axcontlem12
    syl2anc
    3exp2
    com4r
    rexlimiva
    com4l
    3imp2
end
