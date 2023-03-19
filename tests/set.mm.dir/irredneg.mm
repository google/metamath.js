include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cur.mm"
include "cfv.mm"
include "cmulr.mm"
include "co.mm"
include "cbs.mm"
include "eqid.mm"
include "simpl.mm"
include "irredcl.mm"
include "adantl.mm"
include "rngnegr.mm"
include "cui.mm"
include "1unit.mm"
include "unitnegcl.mm"
include "mpdan.mm"
include "adantr.mm"
include "irredrmul.mm"
include "mpd3an3.mm"
include "eqeltrrd.mm"

theorem irredneg
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
  let cB: class B
  let c.0: class .0.
  assume irredn0.i: |- I = ( Irred ` R )
  assume irredneg.n: |- N = ( invg ` R )


  assert |- ( ( R e. Ring /\ X e. I ) -> ( N ` X ) e. I )

  proof
    cR
    crg
    wcel
    #
    cX
    cI
    wcel
    #
    wa
    #
    cX
    cR
    cur
    cfv
    #
    cN
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cX
    cN
    cfv
    cI
    @2
    cR
    cbs
    cfv
    #
    cR
    @5
    @3
    cN
    cX
    @7
    eqid
    #
    @5
    eqid
    #
    @3
    eqid
    #
    irredneg.n
    @0
    @1
    simpl
    @1
    cX
    @7
    wcel
    @0
    @7
    cR
    cI
    cX
    irredn0.i
    @8
    irredcl
    adantl
    rngnegr
    @0
    @1
    @4
    cR
    cui
    cfv
    #
    wcel
    #
    @6
    cI
    wcel
    @0
    @12
    @1
    @0
    @3
    @11
    wcel
    @12
    cR
    @11
    @3
    @11
    eqid
    #
    @10
    1unit
    cR
    @11
    cN
    @3
    @13
    irredneg.n
    unitnegcl
    mpdan
    adantr
    cR
    @5
    @11
    cI
    cX
    @4
    irredn0.i
    @13
    @9
    irredrmul
    mpd3an3
    eqeltrrd
end
