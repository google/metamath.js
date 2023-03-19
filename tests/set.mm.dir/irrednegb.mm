include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "irredneg.mm"
include "adantlr.mm"
include "wceq.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "grpinvinv.mm"
include "sylan.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "impbida.mm"

theorem irrednegb
  let cB: class B
  let cR: class R
  let cI: class I
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.x: class .x.
  let cU: class U
  let cY: class Y
  let c.0: class .0.
  assume irredn0.i: |- I = ( Irred ` R )
  assume irredneg.n: |- N = ( invg ` R )
  assume irrednegb.b: |- B = ( Base ` R )


  assert |- ( ( R e. Ring /\ X e. B ) -> ( X e. I <-> ( N ` X ) e. I ) )

  proof
    cR
    crg
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    cI
    wcel
    #
    cX
    cN
    cfv
    #
    cI
    wcel
    #
    @0
    @3
    @5
    @1
    cR
    cI
    cN
    cX
    irredn0.i
    irredneg.n
    irredneg
    adantlr
    @2
    @5
    wa
    @4
    cN
    cfv
    #
    cX
    cI
    @2
    @6
    cX
    wceq
    #
    @5
    @0
    cR
    cgrp
    wcel
    @1
    @7
    cR
    ringgrp
    cB
    cR
    cN
    cX
    irrednegb.b
    irredneg.n
    grpinvinv
    sylan
    adantr
    @0
    @5
    @6
    cI
    wcel
    @1
    cR
    cI
    cN
    @4
    irredn0.i
    irredneg.n
    irredneg
    adantlr
    eqeltrrd
    impbida
end
