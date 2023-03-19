include "cv.mm"
include "wbr.mm"
include "c-bnj18.mm"
include "wcel.mm"
include "wa.mm"
include "w-bnj15.mm"
include "w3a.mm"
include "w-bnj17.mm"
include "bnj255.mm"
include "df-bnj17.mm"
include "3bitr2i.mm"
include "anbi1i.mm"
include "bitr4i.mm"
include "wss.mm"
include "bnj1125.mm"
include "bnj835.mm"
include "c-bnj14.mm"
include "bnj906.mm"
include "bnj836.mm"
include "bnj1152.mm"
include "biimpri.mm"
include "bnj837.mm"
include "sseldd.mm"
include "sylbir.mm"
include "ex.mm"

theorem bnj1175
  let wch: wff ch
  let wth: wff th
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cX: class X
  assume bnj1175.3: |- C = ( _trCl ( X , A , R ) i^i B )
  assume bnj1175.4: |- ( ch <-> ( ( R _FrSe A /\ X e. A /\ z e. _trCl ( X , A , R ) ) /\ ( R _FrSe A /\ z e. A ) /\ ( w e. A /\ w R z ) ) )
  assume bnj1175.5: |- ( th <-> ( ( R _FrSe A /\ X e. A /\ z e. _trCl ( X , A , R ) ) /\ ( R _FrSe A /\ z e. A ) /\ w e. A ) )


  assert |- ( th -> ( w R z -> w e. _trCl ( X , A , R ) ) )

  proof
    wth
    vw
    cv
    #
    vz
    cv
    #
    cR
    wbr
    #
    @0
    cA
    cR
    cX
    c-bnj18
    #
    wcel
    #
    wth
    @2
    wa
    #
    wch
    @4
    wch
    cA
    cR
    w-bnj15
    #
    cX
    cA
    wcel
    @1
    @3
    wcel
    w3a
    #
    @6
    @1
    cA
    wcel
    wa
    #
    @0
    cA
    wcel
    #
    w3a
    #
    @2
    wa
    #
    @5
    wch
    @7
    @8
    @9
    @2
    wa
    #
    w3a
    @7
    @8
    @9
    @2
    w-bnj17
    @11
    bnj1175.4
    @7
    @8
    @9
    @2
    bnj255
    @7
    @8
    @9
    @2
    df-bnj17
    3bitr2i
    wth
    @10
    @2
    bnj1175.5
    anbi1i
    bitr4i
    wch
    cA
    cR
    @1
    c-bnj18
    #
    @3
    @0
    @7
    @8
    @12
    @13
    @3
    wss
    wch
    bnj1175.4
    cA
    cR
    cX
    @1
    bnj1125
    bnj835
    wch
    cA
    cR
    @1
    c-bnj14
    #
    @13
    @0
    @7
    @8
    @12
    @14
    @13
    wss
    wch
    bnj1175.4
    cA
    cR
    @1
    bnj906
    bnj836
    @7
    @8
    @12
    @0
    @14
    wcel
    #
    wch
    bnj1175.4
    @15
    @12
    cA
    cR
    @1
    @0
    bnj1152
    biimpri
    bnj837
    sseldd
    sseldd
    sylbir
    ex
end
