include "coml.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "clat.mm"
include "omllat.mm"
include "latjcl.mm"
include "syl3an1.mm"
include "3jca.mm"
include "eqid.mm"
include "latlej1.mm"
include "omllaw2N.mm"
include "sylc.mm"

theorem omllaw5N
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume omllaw5.b: |- B = ( Base ` K )
  assume omllaw5.j: |- .\/ = ( join ` K )
  assume omllaw5.m: |- ./\ = ( meet ` K )
  assume omllaw5.o: |- ._|_ = ( oc ` K )


  assert |- ( ( K e. OML /\ X e. B /\ Y e. B ) -> ( X .\/ ( ( ._|_ ` X ) ./\ ( X .\/ Y ) ) ) = ( X .\/ Y ) )

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
    @0
    @1
    cX
    cY
    c.or
    co
    #
    cB
    wcel
    #
    w3a
    cX
    @4
    cK
    cple
    cfv
    #
    wbr
    #
    cX
    cX
    c.pe
    cfv
    @4
    c.an
    co
    c.or
    co
    @4
    wceq
    @3
    @0
    @1
    @5
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @0
    cK
    clat
    wcel
    #
    @1
    @2
    @5
    cK
    omllat
    #
    cB
    c.or
    cK
    cX
    cY
    omllaw5.b
    omllaw5.j
    latjcl
    syl3an1
    3jca
    @0
    @8
    @1
    @2
    @7
    @9
    cB
    c.or
    cK
    @6
    cX
    cY
    omllaw5.b
    @6
    eqid
    #
    omllaw5.j
    latlej1
    syl3an1
    cB
    c.or
    cK
    @6
    c.an
    c.pe
    cX
    @4
    omllaw5.b
    @10
    omllaw5.j
    omllaw5.m
    omllaw5.o
    omllaw2N
    sylc
end
