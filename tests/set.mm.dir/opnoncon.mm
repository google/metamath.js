include "cops.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "cple.mm"
include "wbr.mm"
include "wi.mm"
include "w3a.mm"
include "cjn.mm"
include "co.mm"
include "cp1.mm"
include "eqid.mm"
include "oposlem.mm"
include "3anidm23.mm"
include "simp3d.mm"

theorem opnoncon
  let cB: class B
  let cK: class K
  let c.an: class ./\
  let c.pe: class ._|_
  let cX: class X
  let c.0: class .0.
  assume opnoncon.b: |- B = ( Base ` K )
  assume opnoncon.o: |- ._|_ = ( oc ` K )
  assume opnoncon.m: |- ./\ = ( meet ` K )
  assume opnoncon.z: |- .0. = ( 0. ` K )


  assert |- ( ( K e. OP /\ X e. B ) -> ( X ./\ ( ._|_ ` X ) ) = .0. )

  proof
    cK
    cops
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    cX
    c.pe
    cfv
    #
    cB
    wcel
    @2
    c.pe
    cfv
    cX
    wceq
    cX
    cX
    cK
    cple
    cfv
    #
    wbr
    @2
    @2
    @3
    wbr
    wi
    w3a
    #
    cX
    @2
    cK
    cjn
    cfv
    #
    co
    cK
    cp1
    cfv
    #
    wceq
    #
    cX
    @2
    c.an
    co
    c.0
    wceq
    #
    @0
    @1
    @4
    @7
    @8
    w3a
    cB
    @6
    @5
    cK
    @3
    c.an
    c.pe
    cX
    cX
    c.0
    opnoncon.b
    @3
    eqid
    opnoncon.o
    @5
    eqid
    opnoncon.m
    opnoncon.z
    @6
    eqid
    oposlem
    3anidm23
    simp3d
end
