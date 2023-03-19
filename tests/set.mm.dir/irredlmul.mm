include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "coppr.mm"
include "cfv.mm"
include "cmulr.mm"
include "cbs.mm"
include "eqid.mm"
include "opprmul.mm"
include "opprring.mm"
include "opprirred.mm"
include "opprunit.mm"
include "irredrmul.mm"
include "syl3an1.mm"
include "3com23.mm"
include "syl5eqelr.mm"

theorem irredlmul
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let cI: class I
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.0: class .0.
  assume irredn0.i: |- I = ( Irred ` R )
  assume irredrmul.u: |- U = ( Unit ` R )
  assume irredrmul.t: |- .x. = ( .r ` R )


  assert |- ( ( R e. Ring /\ X e. U /\ Y e. I ) -> ( X .x. Y ) e. I )

  proof
    cR
    crg
    wcel
    #
    cX
    cU
    wcel
    #
    cY
    cI
    wcel
    #
    w3a
    cX
    cY
    c.x
    co
    cY
    cX
    cR
    coppr
    cfv
    #
    cmulr
    cfv
    #
    co
    #
    cI
    cR
    cbs
    cfv
    #
    cR
    @4
    c.x
    @3
    cY
    cX
    @6
    eqid
    irredrmul.t
    @3
    eqid
    #
    @4
    eqid
    #
    opprmul
    @0
    @2
    @1
    @5
    cI
    wcel
    #
    @0
    @3
    crg
    wcel
    @2
    @1
    @9
    cR
    @3
    @7
    opprring
    @3
    @4
    cU
    cI
    cY
    cX
    cR
    @3
    cI
    @7
    irredn0.i
    opprirred
    cR
    @3
    cU
    irredrmul.u
    @7
    opprunit
    @8
    irredrmul
    syl3an1
    3com23
    syl5eqelr
end
