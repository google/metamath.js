include "coml.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "cmt2N.mm"
include "3com23.mm"
include "cmtcomN.mm"
include "cops.mm"
include "omlop.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "syld3an2.mm"
include "3bitr4d.mm"

theorem cmt3N
  let cB: class B
  let cC: class C
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume cmt2.b: |- B = ( Base ` K )
  assume cmt2.o: |- ._|_ = ( oc ` K )
  assume cmt2.c: |- C = ( cm ` K )


  assert |- ( ( K e. OML /\ X e. B /\ Y e. B ) -> ( X C Y <-> ( ._|_ ` X ) C Y ) )

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
    cY
    cX
    cC
    wbr
    #
    cY
    cX
    c.pe
    cfv
    #
    cC
    wbr
    #
    cX
    cY
    cC
    wbr
    @5
    cY
    cC
    wbr
    #
    @0
    @2
    @1
    @4
    @6
    wb
    cB
    cC
    cK
    c.pe
    cY
    cX
    cmt2.b
    cmt2.o
    cmt2.c
    cmt2N
    3com23
    cB
    cC
    cK
    cX
    cY
    cmt2.b
    cmt2.c
    cmtcomN
    @0
    @5
    cB
    wcel
    #
    @1
    @2
    @7
    @6
    wb
    @3
    cK
    cops
    wcel
    #
    @1
    @8
    @0
    @1
    @9
    @2
    cK
    omlop
    3ad2ant1
    @0
    @1
    @2
    simp2
    cB
    cK
    c.pe
    cX
    cmt2.b
    cmt2.o
    opoccl
    syl2anc
    cB
    cC
    cK
    @5
    cY
    cmt2.b
    cmt2.c
    cmtcomN
    syld3an2
    3bitr4d
end
