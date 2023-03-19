include "cops.mm"
include "wcel.mm"
include "w3a.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "eqid.mm"
include "oplecon3b.mm"
include "wb.mm"
include "3com23.mm"
include "notbid.mm"
include "anbi12d.mm"
include "cpo.mm"
include "opposet.mm"
include "pltval3.mm"
include "syl3an1.mm"
include "3ad2ant1.mm"
include "opoccl.mm"
include "3adant2.mm"
include "3adant3.mm"
include "syl3anc.mm"
include "3bitr4d.mm"

theorem opltcon3b
  let cB: class B
  let c.lt: class .<
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume opltcon3.b: |- B = ( Base ` K )
  assume opltcon3.s: |- .< = ( lt ` K )
  assume opltcon3.o: |- ._|_ = ( oc ` K )


  assert |- ( ( K e. OP /\ X e. B /\ Y e. B ) -> ( X .< Y <-> ( ._|_ ` Y ) .< ( ._|_ ` X ) ) )

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
    cK
    cple
    cfv
    #
    wbr
    #
    cY
    cX
    @4
    wbr
    #
    wn
    #
    wa
    #
    cY
    c.pe
    cfv
    #
    cX
    c.pe
    cfv
    #
    @4
    wbr
    #
    @10
    @9
    @4
    wbr
    #
    wn
    #
    wa
    #
    cX
    cY
    c.lt
    wbr
    #
    @9
    @10
    c.lt
    wbr
    #
    @3
    @5
    @11
    @7
    @13
    cB
    cK
    @4
    c.pe
    cX
    cY
    opltcon3.b
    @4
    eqid
    #
    opltcon3.o
    oplecon3b
    @3
    @6
    @12
    @0
    @2
    @1
    @6
    @12
    wb
    cB
    cK
    @4
    c.pe
    cY
    cX
    opltcon3.b
    @17
    opltcon3.o
    oplecon3b
    3com23
    notbid
    anbi12d
    @0
    cK
    cpo
    wcel
    #
    @1
    @2
    @15
    @8
    wb
    cK
    opposet
    #
    cB
    c.lt
    cK
    @4
    cX
    cY
    opltcon3.b
    @17
    opltcon3.s
    pltval3
    syl3an1
    @3
    @18
    @9
    cB
    wcel
    #
    @10
    cB
    wcel
    #
    @16
    @14
    wb
    @0
    @1
    @18
    @2
    @19
    3ad2ant1
    @0
    @2
    @20
    @1
    cB
    cK
    c.pe
    cY
    opltcon3.b
    opltcon3.o
    opoccl
    3adant2
    @0
    @1
    @21
    @2
    cB
    cK
    c.pe
    cX
    opltcon3.b
    opltcon3.o
    opoccl
    3adant3
    cB
    c.lt
    cK
    @4
    @9
    @10
    opltcon3.b
    @17
    opltcon3.s
    pltval3
    syl3anc
    3bitr4d
end
