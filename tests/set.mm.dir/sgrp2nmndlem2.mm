include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt2.mm"
include "cplusg.mm"
include "cfv.mm"
include "eqtri.mm"
include "a1i.mm"
include "iftrue.mm"
include "ad2antrl.mm"
include "simpl.mm"
include "simpr.mm"
include "ovmpt2d.mm"

theorem sgrp2nmndlem2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cM: class M
  let c.op: class .o.
  let va: setvar a
  let vb: setvar b
  assume mgm2nsgrp.s: |- S = { A , B }
  assume mgm2nsgrp.b: |- ( Base ` M ) = S
  assume sgrp2nmnd.o: |- ( +g ` M ) = ( x e. S , y e. S |-> if ( x = A , A , B ) )
  assume sgrp2nmnd.p: |- .o. = ( +g ` M )

  disjoint C x
  disjoint C y
  disjoint x y
  disjoint S x
  disjoint S y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint M x
  disjoint M a
  disjoint M b
  disjoint a b
  disjoint S a
  disjoint S b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  assert |- ( ( A e. S /\ C e. S ) -> ( A .o. C ) = A )

  proof
    cA
    cS
    wcel
    #
    cC
    cS
    wcel
    #
    wa
    #
    vx
    vy
    cA
    cC
    cS
    cS
    vx
    cv
    cA
    wceq
    #
    cA
    cB
    cif
    #
    cA
    c.op
    cS
    c.op
    vx
    vy
    cS
    cS
    @4
    cmpt2
    #
    wceq
    @2
    c.op
    cM
    cplusg
    cfv
    @5
    sgrp2nmnd.p
    sgrp2nmnd.o
    eqtri
    a1i
    @3
    @4
    cA
    wceq
    @2
    vy
    cv
    cC
    wceq
    @3
    cA
    cB
    iftrue
    ad2antrl
    @0
    @1
    simpl
    #
    @0
    @1
    simpr
    @6
    ovmpt2d
end
