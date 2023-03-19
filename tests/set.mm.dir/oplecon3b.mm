include "cops.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "cfv.mm"
include "oplecon3.mm"
include "wi.mm"
include "simp1.mm"
include "opoccl.mm"
include "3adant2.mm"
include "3adant3.mm"
include "syl3anc.mm"
include "wceq.mm"
include "opococ.mm"
include "breq12d.mm"
include "sylibd.mm"
include "impbid.mm"

theorem oplecon3b
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume opcon3.b: |- B = ( Base ` K )
  assume opcon3.l: |- .<_ = ( le ` K )
  assume opcon3.o: |- ._|_ = ( oc ` K )


  assert |- ( ( K e. OP /\ X e. B /\ Y e. B ) -> ( X .<_ Y <-> ( ._|_ ` Y ) .<_ ( ._|_ ` X ) ) )

  proof
    cK
    cops
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
    c.pe
    cfv
    #
    cX
    c.pe
    cfv
    #
    c.le
    wbr
    #
    cB
    cK
    c.le
    c.pe
    cX
    cY
    opcon3.b
    opcon3.l
    opcon3.o
    oplecon3
    @3
    @7
    @6
    c.pe
    cfv
    #
    @5
    c.pe
    cfv
    #
    c.le
    wbr
    #
    @4
    @3
    @0
    @5
    cB
    wcel
    #
    @6
    cB
    wcel
    #
    @7
    @10
    wi
    @0
    @1
    @2
    simp1
    @0
    @2
    @11
    @1
    cB
    cK
    c.pe
    cY
    opcon3.b
    opcon3.o
    opoccl
    3adant2
    @0
    @1
    @12
    @2
    cB
    cK
    c.pe
    cX
    opcon3.b
    opcon3.o
    opoccl
    3adant3
    cB
    cK
    c.le
    c.pe
    @5
    @6
    opcon3.b
    opcon3.l
    opcon3.o
    oplecon3
    syl3anc
    @3
    @8
    cX
    @9
    cY
    c.le
    @0
    @1
    @8
    cX
    wceq
    @2
    cB
    cK
    c.pe
    cX
    opcon3.b
    opcon3.o
    opococ
    3adant3
    @0
    @2
    @9
    cY
    wceq
    @1
    cB
    cK
    c.pe
    cY
    opcon3.b
    opcon3.o
    opococ
    3adant2
    breq12d
    sylibd
    impbid
end
