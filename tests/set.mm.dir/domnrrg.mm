include "cdomn.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "csn.mm"
include "cdif.mm"
include "wss.mm"
include "cnzr.mm"
include "isdomn2.mm"
include "simprbi.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "sseldd.mm"

theorem domnrrg
  let cB: class B
  let cR: class R
  let cE: class E
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume isdomn2.b: |- B = ( Base ` R )
  assume isdomn2.t: |- E = ( RLReg ` R )
  assume isdomn2.z: |- .0. = ( 0g ` R )


  assert |- ( ( R e. Domn /\ X e. B /\ X =/= .0. ) -> X e. E )

  proof
    cR
    cdomn
    wcel
    #
    cX
    cB
    wcel
    #
    cX
    c.0
    wne
    #
    w3a
    #
    cB
    c.0
    csn
    cdif
    #
    cE
    cX
    @0
    @1
    @4
    cE
    wss
    #
    @2
    @0
    cR
    cnzr
    wcel
    @5
    cB
    cR
    cE
    c.0
    isdomn2.b
    isdomn2.t
    isdomn2.z
    isdomn2
    simprbi
    3ad2ant1
    @3
    @1
    @2
    cX
    @4
    wcel
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    cX
    cB
    c.0
    eldifsn
    sylanbrc
    sseldd
end
