include "cpo.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "wn.mm"
include "wi.mm"
include "cvrnbtwn.mm"
include "wne.mm"
include "wb.mm"
include "pltval.mm"
include "3adant3r2.mm"
include "3adant3.mm"
include "anbi1d.mm"
include "notbid.mm"
include "an32.mm"
include "df-ne.mm"
include "anbi2i.mm"
include "bitri.mm"
include "notbii.mm"
include "iman.mm"
include "bitr4i.mm"
include "syl6bb.mm"
include "mpbid.mm"
include "posref.mm"
include "breq2.mm"
include "syl5ibcom.mm"
include "3ad2antr1.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "simp3.mm"
include "cvrlt.mm"
include "syl31anc.mm"
include "breq1.mm"
include "jcad.mm"
include "impbid.mm"

theorem cvrnbtwn3
  let cB: class B
  let cC: class C
  let c.lt: class .<
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let cA: class A
  let vz: setvar z
  assume cvrletr.b: |- B = ( Base ` K )
  assume cvrletr.l: |- .<_ = ( le ` K )
  assume cvrletr.s: |- .< = ( lt ` K )
  assume cvrletr.c: |- C = ( <o ` K )


  assert |- ( ( K e. Poset /\ ( X e. B /\ Y e. B /\ Z e. B ) /\ X C Y ) -> ( ( X .<_ Z /\ Z .< Y ) <-> X = Z ) )

  proof
    cK
    cpo
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
    cY
    cC
    wbr
    #
    w3a
    #
    cX
    cZ
    c.le
    wbr
    #
    cZ
    cY
    c.lt
    wbr
    #
    wa
    #
    cX
    cZ
    wceq
    #
    @6
    cX
    cZ
    c.lt
    wbr
    #
    @8
    wa
    #
    wn
    #
    @9
    @10
    wi
    #
    cpo
    cB
    cC
    c.lt
    cK
    cX
    cY
    cZ
    cvrletr.b
    cvrletr.s
    cvrletr.c
    cvrnbtwn
    @6
    @13
    @7
    cX
    cZ
    wne
    #
    wa
    #
    @8
    wa
    #
    wn
    #
    @14
    @6
    @12
    @17
    @6
    @11
    @16
    @8
    @0
    @4
    @11
    @16
    wb
    #
    @5
    @0
    @1
    @3
    @19
    @2
    cpo
    cB
    cB
    c.lt
    cK
    c.le
    cX
    cZ
    cvrletr.l
    cvrletr.s
    pltval
    3adant3r2
    3adant3
    anbi1d
    notbid
    @18
    @9
    @10
    wn
    #
    wa
    #
    wn
    @14
    @17
    @21
    @17
    @9
    @15
    wa
    @21
    @7
    @15
    @8
    an32
    @15
    @20
    @9
    cX
    cZ
    df-ne
    anbi2i
    bitri
    notbii
    @9
    @10
    iman
    bitr4i
    syl6bb
    mpbid
    @6
    @10
    @7
    @8
    @0
    @4
    @10
    @7
    wi
    #
    @5
    @0
    @2
    @1
    @22
    @3
    @0
    @1
    wa
    cX
    cX
    c.le
    wbr
    @10
    @7
    cB
    cK
    c.le
    cX
    cvrletr.b
    cvrletr.l
    posref
    cX
    cZ
    cX
    c.le
    breq2
    syl5ibcom
    3ad2antr1
    3adant3
    @6
    cX
    cY
    c.lt
    wbr
    #
    @10
    @8
    @6
    @0
    @1
    @2
    @5
    @23
    @0
    @4
    @5
    simp1
    @0
    @1
    @2
    @3
    @5
    simp21
    @0
    @1
    @2
    @3
    @5
    simp22
    @0
    @4
    @5
    simp3
    cpo
    cB
    cC
    c.lt
    cK
    cX
    cY
    cvrletr.b
    cvrletr.s
    cvrletr.c
    cvrlt
    syl31anc
    cX
    cZ
    cY
    c.lt
    breq1
    syl5ibcom
    jcad
    impbid
end
