include "w-bnj15.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "c-bnj14.mm"
include "c-bnj18.mm"
include "wss.mm"
include "wral.mm"
include "w-bnj19.mm"
include "wi.mm"
include "wal.mm"
include "w-bnj17.mm"
include "sylbir.mm"
include "gen2.mm"
include "w3a.mm"
include "bnj253.mm"
include "imbi1i.mm"
include "2albii.mm"
include "3impexp.mm"
include "19.21v.mm"
include "imbi2i.mm"
include "bitri.mm"
include "albii.mm"
include "df-ral.mm"
include "bicomi.mm"
include "3bitri.mm"
include "mpbi.mm"
include "dfss2.mm"
include "ralbii.mm"
include "sylibr.mm"
include "df-bnj19.mm"

theorem bnj978
  let wth: wff th
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  let cX: class X
  assume bnj978.1: |- ( th <-> ( R _FrSe A /\ X e. A /\ y e. _trCl ( X , A , R ) /\ z e. _pred ( y , A , R ) ) )
  assume bnj978.2: |- ( th -> z e. _trCl ( X , A , R ) )

  disjoint A y
  disjoint A z
  disjoint y z
  disjoint R y
  disjoint R z
  disjoint X y
  disjoint X z
  assert |- ( ( R _FrSe A /\ X e. A ) -> _TrFo ( _trCl ( X , A , R ) , A , R ) )

  proof
    cA
    cR
    w-bnj15
    #
    cX
    cA
    wcel
    #
    wa
    #
    cA
    cR
    vy
    cv
    #
    c-bnj14
    #
    cA
    cR
    cX
    c-bnj18
    #
    wss
    #
    vy
    @5
    wral
    #
    cA
    @5
    cR
    w-bnj19
    @2
    vz
    cv
    #
    @4
    wcel
    #
    @8
    @5
    wcel
    #
    wi
    #
    vz
    wal
    #
    vy
    @5
    wral
    #
    @7
    @0
    @1
    @3
    @5
    wcel
    #
    @9
    w-bnj17
    #
    @10
    wi
    #
    vz
    wal
    vy
    wal
    #
    @2
    @13
    wi
    #
    @16
    vy
    vz
    @15
    wth
    @10
    bnj978.1
    bnj978.2
    sylbir
    gen2
    @17
    @2
    @14
    @9
    w3a
    #
    @10
    wi
    #
    vz
    wal
    vy
    wal
    @2
    @14
    @11
    wi
    #
    wi
    #
    vz
    wal
    #
    vy
    wal
    #
    @18
    @16
    @20
    vy
    vz
    @15
    @19
    @10
    @0
    @1
    @14
    @9
    bnj253
    imbi1i
    2albii
    @20
    @22
    vy
    vz
    @2
    @14
    @9
    @10
    3impexp
    2albii
    @24
    @2
    @14
    @12
    wi
    #
    wi
    #
    vy
    wal
    @2
    @25
    vy
    wal
    #
    wi
    @18
    @23
    @26
    vy
    @23
    @2
    @21
    vz
    wal
    #
    wi
    @26
    @2
    @21
    vz
    19.21v
    @28
    @25
    @2
    @14
    @11
    vz
    19.21v
    imbi2i
    bitri
    albii
    @2
    @25
    vy
    19.21v
    @27
    @13
    @2
    @13
    @27
    @12
    vy
    @5
    df-ral
    bicomi
    imbi2i
    3bitri
    3bitri
    mpbi
    @6
    @12
    vy
    @5
    vz
    @4
    @5
    dfss2
    ralbii
    sylibr
    vy
    cA
    @5
    cR
    df-bnj19
    sylibr
end
