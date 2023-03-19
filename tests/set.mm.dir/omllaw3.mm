include "coml.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cjn.mm"
include "oveq2.mm"
include "adantl.mm"
include "col.mm"
include "omlol.mm"
include "eqid.mm"
include "olj01.mm"
include "sylan.mm"
include "3adant3.mm"
include "adantr.mm"
include "eqtr2d.mm"
include "adantrl.mm"
include "omllaw.mm"
include "imp.mm"
include "adantrr.mm"
include "eqtr4d.mm"
include "ex.mm"

theorem omllaw3
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume omllaw3.b: |- B = ( Base ` K )
  assume omllaw3.l: |- .<_ = ( le ` K )
  assume omllaw3.m: |- ./\ = ( meet ` K )
  assume omllaw3.o: |- ._|_ = ( oc ` K )
  assume omllaw3.z: |- .0. = ( 0. ` K )


  assert |- ( ( K e. OML /\ X e. B /\ Y e. B ) -> ( ( X .<_ Y /\ ( Y ./\ ( ._|_ ` X ) ) = .0. ) -> X = Y ) )

  proof
    cK
    coml
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    c.le
    wbr
    #
    cY
    cX
    c.pe
    cfv
    c.an
    co
    #
    c.0
    wceq
    #
    wa
    #
    cX
    cY
    wceq
    @3
    @7
    wa
    cX
    cX
    @5
    cK
    cjn
    cfv
    #
    co
    #
    cY
    @3
    @6
    cX
    @9
    wceq
    @4
    @3
    @6
    wa
    @9
    cX
    c.0
    @8
    co
    #
    cX
    @6
    @9
    @10
    wceq
    @3
    @5
    c.0
    cX
    @8
    oveq2
    adantl
    @3
    @10
    cX
    wceq
    #
    @6
    @0
    @1
    @11
    @2
    @0
    cK
    col
    wcel
    @1
    @11
    cK
    omlol
    cB
    @8
    cK
    cX
    c.0
    omllaw3.b
    @8
    eqid
    #
    omllaw3.z
    olj01
    sylan
    3adant3
    adantr
    eqtr2d
    adantrl
    @3
    @4
    cY
    @9
    wceq
    #
    @6
    @3
    @4
    @13
    cB
    @8
    cK
    c.le
    c.an
    c.pe
    cX
    cY
    omllaw3.b
    omllaw3.l
    @12
    omllaw3.m
    omllaw3.o
    omllaw
    imp
    adantrr
    eqtr4d
    ex
end
