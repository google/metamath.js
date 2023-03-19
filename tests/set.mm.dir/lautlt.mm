include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wne.mm"
include "wb.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "eqid.mm"
include "lautle.mm"
include "syl22anc.mm"
include "wceq.mm"
include "laut11.mm"
include "bicomd.mm"
include "necon3bid.mm"
include "anbi12d.mm"
include "pltval.mm"
include "3adant3r1.mm"
include "lautcl.mm"
include "syl21anc.mm"
include "syl3anc.mm"
include "3bitr4d.mm"

theorem lautlt
  let cA: class A
  let cB: class B
  let c.lt: class .<
  let cF: class F
  let cI: class I
  let cK: class K
  let cX: class X
  let cY: class Y
  assume lautlt.b: |- B = ( Base ` K )
  assume lautlt.s: |- .< = ( lt ` K )
  assume lautlt.i: |- I = ( LAut ` K )


  assert |- ( ( K e. A /\ ( F e. I /\ X e. B /\ Y e. B ) ) -> ( X .< Y <-> ( F ` X ) .< ( F ` Y ) ) )

  proof
    cK
    cA
    wcel
    #
    cF
    cI
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
    wa
    #
    cX
    cY
    cK
    cple
    cfv
    #
    wbr
    #
    cX
    cY
    wne
    #
    wa
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    @6
    wbr
    #
    @10
    @11
    wne
    #
    wa
    #
    cX
    cY
    c.lt
    wbr
    #
    @10
    @11
    c.lt
    wbr
    #
    @5
    @7
    @12
    @8
    @13
    @5
    @0
    @1
    @2
    @3
    @7
    @12
    wb
    @0
    @4
    simpl
    #
    @0
    @1
    @2
    @3
    simpr1
    #
    @0
    @1
    @2
    @3
    simpr2
    #
    @0
    @1
    @2
    @3
    simpr3
    #
    cB
    cF
    cI
    cK
    @6
    cA
    cX
    cY
    lautlt.b
    @6
    eqid
    #
    lautlt.i
    lautle
    syl22anc
    @5
    cX
    cY
    @10
    @11
    @5
    @10
    @11
    wceq
    #
    cX
    cY
    wceq
    #
    @5
    @0
    @1
    @2
    @3
    @22
    @23
    wb
    @17
    @18
    @19
    @20
    cB
    cF
    cI
    cK
    cA
    cX
    cY
    lautlt.b
    lautlt.i
    laut11
    syl22anc
    bicomd
    necon3bid
    anbi12d
    @0
    @2
    @3
    @15
    @9
    wb
    @1
    cA
    cB
    cB
    c.lt
    cK
    @6
    cX
    cY
    @21
    lautlt.s
    pltval
    3adant3r1
    @5
    @0
    @10
    cB
    wcel
    #
    @11
    cB
    wcel
    #
    @16
    @14
    wb
    @17
    @5
    @0
    @1
    @2
    @24
    @17
    @18
    @19
    cB
    cF
    cI
    cK
    cA
    cX
    lautlt.b
    lautlt.i
    lautcl
    syl21anc
    @5
    @0
    @1
    @3
    @25
    @17
    @18
    @20
    cB
    cF
    cI
    cK
    cA
    cY
    lautlt.b
    lautlt.i
    lautcl
    syl21anc
    cA
    cB
    cB
    c.lt
    cK
    @6
    @10
    @11
    @21
    lautlt.s
    pltval
    syl3anc
    3bitr4d
end
