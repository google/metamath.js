include "cv.mm"
include "cdif.mm"
include "cun.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "elun.mm"
include "eldif.mm"
include "orbi2i.mm"
include "bitri.mm"
include "idn1.mm"
include "orc.mm"
include "e1a.mm"
include "olc.mm"
include "pm3.2.mm"
include "e11.mm"
include "in1.mm"
include "simpl.mm"
include "simpr.mm"
include "jaoi.mm"
include "anddi.mm"
include "bicomi.mm"
include "orcd.mm"
include "sylbir.mm"
include "impbii.mm"
include "notbii.mm"
include "pm4.53.mm"
include "anbi12i.mm"
include "bitr4i.mm"
include "ax-gen.mm"
include "dfcleq.mm"
include "biimpri.mm"
include "e0a.mm"

theorem undif3VD
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A u. ( B \ C ) ) = ( ( A u. B ) \ ( C \ A ) )

  proof
    vx
    cv
    #
    cA
    cB
    cC
    cdif
    #
    cun
    #
    wcel
    #
    @0
    cA
    cB
    cun
    #
    cC
    cA
    cdif
    #
    cdif
    #
    wcel
    #
    wb
    #
    vx
    wal
    #
    @2
    @6
    wceq
    #
    @8
    vx
    @3
    @0
    cA
    wcel
    #
    @0
    cB
    wcel
    #
    wo
    #
    @0
    cC
    wcel
    #
    wn
    #
    @11
    wo
    #
    wa
    #
    @7
    @3
    @11
    @12
    @15
    wa
    #
    wo
    #
    @17
    @3
    @11
    @0
    @1
    wcel
    #
    wo
    @19
    @0
    cA
    @1
    elun
    @20
    @18
    @11
    @0
    cB
    cC
    eldif
    orbi2i
    bitri
    @19
    @17
    @11
    @17
    @18
    @11
    @17
    @11
    @13
    @16
    @17
    @11
    @11
    @13
    @11
    idn1
    #
    @11
    @12
    orc
    e1a
    @11
    @11
    @16
    @21
    @11
    @15
    olc
    e1a
    @13
    @16
    pm3.2
    #
    e11
    in1
    @18
    @17
    @18
    @13
    @16
    @17
    @18
    @12
    @13
    @18
    @18
    @12
    @18
    idn1
    #
    @12
    @15
    simpl
    e1a
    @12
    @11
    olc
    e1a
    @18
    @15
    @16
    @18
    @18
    @15
    @23
    @12
    @15
    simpr
    e1a
    @15
    @11
    orc
    e1a
    @22
    e11
    in1
    jaoi
    @17
    @11
    @15
    wa
    #
    @11
    @11
    wa
    #
    wo
    #
    @18
    @12
    @11
    wa
    #
    wo
    #
    wo
    #
    @19
    @17
    @29
    @11
    @12
    @15
    @11
    anddi
    bicomi
    @26
    @19
    @28
    @24
    @19
    @25
    @24
    @19
    @24
    @24
    @19
    @24
    idn1
    @24
    @11
    @18
    @11
    @15
    simpl
    orcd
    e1a
    in1
    @25
    @19
    @25
    @11
    @19
    @25
    @25
    @11
    @25
    idn1
    @11
    @11
    simpl
    e1a
    @11
    @18
    orc
    #
    e1a
    in1
    jaoi
    @18
    @19
    @27
    @18
    @19
    @18
    @18
    @19
    @23
    @18
    @11
    olc
    e1a
    in1
    @27
    @19
    @27
    @11
    @19
    @27
    @27
    @11
    @27
    idn1
    @12
    @11
    simpr
    e1a
    @30
    e1a
    in1
    jaoi
    jaoi
    sylbir
    impbii
    bitri
    @7
    @0
    @4
    wcel
    #
    @0
    @5
    wcel
    #
    wn
    #
    wa
    @17
    @0
    @4
    @5
    eldif
    @31
    @13
    @33
    @16
    @0
    cA
    cB
    elun
    @33
    @14
    @11
    wn
    wa
    #
    wn
    @16
    @32
    @34
    @0
    cC
    cA
    eldif
    notbii
    @14
    @11
    pm4.53
    bitri
    anbi12i
    bitri
    bitr4i
    ax-gen
    @10
    @9
    vx
    @2
    @6
    dfcleq
    biimpri
    e0a
end
