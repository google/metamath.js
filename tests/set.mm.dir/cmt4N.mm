include "coml.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "cfv.mm"
include "cmt2N.mm"
include "wb.mm"
include "cops.mm"
include "omlop.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "cmt3N.mm"
include "syld3an3.mm"
include "bitrd.mm"

theorem cmt4N
  let cB: class B
  let cC: class C
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume cmt2.b: |- B = ( Base ` K )
  assume cmt2.o: |- ._|_ = ( oc ` K )
  assume cmt2.c: |- C = ( cm ` K )


  assert |- ( ( K e. OML /\ X e. B /\ Y e. B ) -> ( X C Y <-> ( ._|_ ` X ) C ( ._|_ ` Y ) ) )

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
    cC
    wbr
    cX
    cY
    c.pe
    cfv
    #
    cC
    wbr
    #
    cX
    c.pe
    cfv
    @4
    cC
    wbr
    #
    cB
    cC
    cK
    c.pe
    cX
    cY
    cmt2.b
    cmt2.o
    cmt2.c
    cmt2N
    @0
    @1
    @2
    @4
    cB
    wcel
    #
    @5
    @6
    wb
    @3
    cK
    cops
    wcel
    #
    @2
    @7
    @0
    @1
    @8
    @2
    cK
    omlop
    3ad2ant1
    @0
    @1
    @2
    simp3
    cB
    cK
    c.pe
    cY
    cmt2.b
    cmt2.o
    opoccl
    syl2anc
    cB
    cC
    cK
    c.pe
    cX
    @4
    cmt2.b
    cmt2.o
    cmt2.c
    cmt3N
    syld3an3
    bitrd
end
