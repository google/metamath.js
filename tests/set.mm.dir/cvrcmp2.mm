include "cops.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "coc.mm"
include "cfv.mm"
include "wceq.mm"
include "cpo.mm"
include "wb.mm"
include "opposet.mm"
include "3ad2ant1.mm"
include "simp1.mm"
include "simp22.mm"
include "eqid.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "simp21.mm"
include "simp23.mm"
include "cvrcon3b.mm"
include "3adant3r2.mm"
include "3adant3r1.mm"
include "anbi12d.mm"
include "biimp3a.mm"
include "ancomd.mm"
include "cvrcmp.mm"
include "syl131anc.mm"
include "oplecon3b.mm"
include "syl3anc.mm"
include "opcon3b.mm"
include "3bitr4d.mm"

theorem cvrcmp2
  let cB: class B
  let cC: class C
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume cvrcmp.b: |- B = ( Base ` K )
  assume cvrcmp.l: |- .<_ = ( le ` K )
  assume cvrcmp.c: |- C = ( <o ` K )


  assert |- ( ( K e. OP /\ ( X e. B /\ Y e. B /\ Z e. B ) /\ ( X C Z /\ Y C Z ) ) -> ( X .<_ Y <-> X = Y ) )

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
    cZ
    cB
    wcel
    #
    w3a
    #
    cX
    cZ
    cC
    wbr
    #
    cY
    cZ
    cC
    wbr
    #
    wa
    #
    w3a
    #
    cY
    cK
    coc
    cfv
    #
    cfv
    #
    cX
    @9
    cfv
    #
    c.le
    wbr
    #
    @10
    @11
    wceq
    #
    cX
    cY
    c.le
    wbr
    #
    cX
    cY
    wceq
    #
    @8
    cK
    cpo
    wcel
    #
    @10
    cB
    wcel
    #
    @11
    cB
    wcel
    #
    cZ
    @9
    cfv
    #
    cB
    wcel
    #
    @19
    @10
    cC
    wbr
    #
    @19
    @11
    cC
    wbr
    #
    wa
    @12
    @13
    wb
    @0
    @4
    @16
    @7
    cK
    opposet
    3ad2ant1
    @8
    @0
    @2
    @17
    @0
    @4
    @7
    simp1
    #
    @0
    @1
    @2
    @3
    @7
    simp22
    #
    cB
    cK
    @9
    cY
    cvrcmp.b
    @9
    eqid
    #
    opoccl
    syl2anc
    @8
    @0
    @1
    @18
    @23
    @0
    @1
    @2
    @3
    @7
    simp21
    #
    cB
    cK
    @9
    cX
    cvrcmp.b
    @25
    opoccl
    syl2anc
    @8
    @0
    @3
    @20
    @23
    @0
    @1
    @2
    @3
    @7
    simp23
    cB
    cK
    @9
    cZ
    cvrcmp.b
    @25
    opoccl
    syl2anc
    @8
    @22
    @21
    @0
    @4
    @7
    @22
    @21
    wa
    @0
    @4
    wa
    @5
    @22
    @6
    @21
    @0
    @1
    @3
    @5
    @22
    wb
    @2
    cB
    cC
    cK
    @9
    cX
    cZ
    cvrcmp.b
    @25
    cvrcmp.c
    cvrcon3b
    3adant3r2
    @0
    @2
    @3
    @6
    @21
    wb
    @1
    cB
    cC
    cK
    @9
    cY
    cZ
    cvrcmp.b
    @25
    cvrcmp.c
    cvrcon3b
    3adant3r1
    anbi12d
    biimp3a
    ancomd
    cB
    cC
    cK
    c.le
    @10
    @11
    @19
    cvrcmp.b
    cvrcmp.l
    cvrcmp.c
    cvrcmp
    syl131anc
    @8
    @0
    @1
    @2
    @14
    @12
    wb
    @23
    @26
    @24
    cB
    cK
    c.le
    @9
    cX
    cY
    cvrcmp.b
    cvrcmp.l
    @25
    oplecon3b
    syl3anc
    @8
    @0
    @1
    @2
    @15
    @13
    wb
    @23
    @26
    @24
    cB
    cK
    @9
    cX
    cY
    cvrcmp.b
    @25
    opcon3b
    syl3anc
    3bitr4d
end
