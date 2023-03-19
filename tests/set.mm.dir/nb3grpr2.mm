include "cpr.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cnbgr.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "3anan32.mm"
include "a1i.mm"
include "prcom.mm"
include "eleq1i.mm"
include "biimpi.mm"
include "pm4.71i.mm"
include "anbi2i.mm"
include "anass.mm"
include "bitr4i.mm"
include "anbi1i.mm"
include "bitri.mm"
include "syl6bb.mm"
include "df-3an.mm"
include "3anass.mm"
include "anbi12i.mm"
include "an6.mm"
include "nb3grprlem1.mm"
include "ctp.mm"
include "tpcoma.mm"
include "syl6eq.mm"
include "3ancoma.mm"
include "sylib.mm"
include "tprot.mm"
include "syl6eqr.mm"
include "3anrot.mm"
include "sylibr.mm"
include "3anbi123d.mm"
include "bitr4d.mm"

theorem nb3grpr2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume nb3grpr.v: |- V = ( Vtx ` G )
  assume nb3grpr.e: |- E = ( Edg ` G )
  assume nb3grpr.g: |- ( ph -> G e. USGraph )
  assume nb3grpr.t: |- ( ph -> V = { A , B , C } )
  assume nb3grpr.s: |- ( ph -> ( A e. X /\ B e. Y /\ C e. Z ) )
  assume nb3grpr.n: |- ( ph -> ( A =/= B /\ A =/= C /\ B =/= C ) )


  assert |- ( ph -> ( ( { A , B } e. E /\ { B , C } e. E /\ { C , A } e. E ) <-> ( ( G NeighbVtx A ) = { B , C } /\ ( G NeighbVtx B ) = { A , C } /\ ( G NeighbVtx C ) = { A , B } ) ) )

  proof
    wph
    cA
    cB
    cpr
    #
    cE
    wcel
    #
    cB
    cC
    cpr
    #
    cE
    wcel
    #
    cC
    cA
    cpr
    #
    cE
    wcel
    #
    w3a
    #
    @1
    cA
    cC
    cpr
    #
    cE
    wcel
    #
    wa
    #
    cB
    cA
    cpr
    #
    cE
    wcel
    #
    @3
    wa
    #
    @5
    cC
    cB
    cpr
    #
    cE
    wcel
    #
    wa
    #
    w3a
    #
    cG
    cA
    cnbgr
    co
    @2
    wceq
    #
    cG
    cB
    cnbgr
    co
    @7
    wceq
    #
    cG
    cC
    cnbgr
    co
    @0
    wceq
    #
    w3a
    wph
    @6
    @1
    @5
    wa
    #
    @8
    @3
    wa
    #
    wa
    #
    @16
    wph
    @6
    @20
    @3
    wa
    #
    @22
    @6
    @23
    wb
    wph
    @1
    @3
    @5
    3anan32
    a1i
    @23
    @20
    @8
    wa
    #
    @3
    wa
    @22
    @20
    @24
    @3
    @20
    @1
    @5
    @8
    wa
    #
    wa
    @24
    @5
    @25
    @1
    @5
    @8
    @5
    @8
    @4
    @7
    cE
    cC
    cA
    prcom
    eleq1i
    biimpi
    pm4.71i
    anbi2i
    @1
    @5
    @8
    anass
    bitr4i
    anbi1i
    @20
    @8
    @3
    anass
    bitri
    syl6bb
    @22
    @1
    @11
    @5
    w3a
    #
    @8
    @3
    @14
    w3a
    #
    wa
    @16
    @20
    @26
    @21
    @27
    @20
    @1
    @11
    wa
    #
    @5
    wa
    @26
    @1
    @28
    @5
    @1
    @11
    @1
    @11
    @0
    @10
    cE
    cA
    cB
    prcom
    eleq1i
    biimpi
    pm4.71i
    anbi1i
    @1
    @11
    @5
    df-3an
    bitr4i
    @21
    @8
    @3
    @14
    wa
    #
    wa
    @27
    @3
    @29
    @8
    @3
    @14
    @3
    @14
    @2
    @13
    cE
    cB
    cC
    prcom
    eleq1i
    biimpi
    pm4.71i
    anbi2i
    @8
    @3
    @14
    3anass
    bitr4i
    anbi12i
    @1
    @11
    @5
    @8
    @3
    @14
    an6
    bitri
    syl6bb
    wph
    @17
    @9
    @18
    @12
    @19
    @15
    wph
    cA
    cB
    cC
    cE
    cG
    cV
    cX
    cY
    cZ
    nb3grpr.v
    nb3grpr.e
    nb3grpr.g
    nb3grpr.t
    nb3grpr.s
    nb3grprlem1
    wph
    cB
    cA
    cC
    cE
    cG
    cV
    cY
    cX
    cZ
    nb3grpr.v
    nb3grpr.e
    nb3grpr.g
    wph
    cV
    cA
    cB
    cC
    ctp
    #
    cB
    cA
    cC
    ctp
    nb3grpr.t
    cA
    cB
    cC
    tpcoma
    syl6eq
    wph
    cA
    cX
    wcel
    #
    cB
    cY
    wcel
    #
    cC
    cZ
    wcel
    #
    w3a
    #
    @32
    @31
    @33
    w3a
    nb3grpr.s
    @31
    @32
    @33
    3ancoma
    sylib
    nb3grprlem1
    wph
    cC
    cA
    cB
    cE
    cG
    cV
    cZ
    cX
    cY
    nb3grpr.v
    nb3grpr.e
    nb3grpr.g
    wph
    cV
    @30
    cC
    cA
    cB
    ctp
    nb3grpr.t
    cC
    cA
    cB
    tprot
    syl6eqr
    wph
    @34
    @33
    @31
    @32
    w3a
    nb3grpr.s
    @33
    @31
    @32
    3anrot
    sylibr
    nb3grprlem1
    3anbi123d
    bitr4d
end
