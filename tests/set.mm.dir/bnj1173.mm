include "cv.mm"
include "wcel.mm"
include "w3a.mm"
include "w-bnj15.mm"
include "wa.mm"
include "c-bnj18.mm"
include "3simpc.mm"
include "wi.mm"
include "3adant3.mm"
include "cin.mm"
include "elin.mm"
include "simplbi.mm"
include "eleq2s.mm"
include "3ad2ant3.mm"
include "pm3.21.mm"
include "syl3anc.mm"
include "bnj170.mm"
include "syl6ibr.mm"
include "impbid2.mm"
include "syl5bb.mm"
include "bnj1147.mm"
include "bnj1213.mm"
include "jca.mm"
include "biantrurd.mm"
include "bitr4d.mm"

theorem bnj1173
  let wph: wff ph
  let wps: wff ps
  let wth: wff th
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cX: class X
  assume bnj1173.3: |- C = ( _trCl ( X , A , R ) i^i B )
  assume bnj1173.5: |- ( th <-> ( ( R _FrSe A /\ X e. A /\ z e. _trCl ( X , A , R ) ) /\ ( R _FrSe A /\ z e. A ) /\ w e. A ) )
  assume bnj1173.9: |- ( ( ph /\ ps ) -> R _FrSe A )
  assume bnj1173.17: |- ( ( ph /\ ps ) -> X e. A )


  assert |- ( ( ph /\ ps /\ z e. C ) -> ( th <-> w e. A ) )

  proof
    wph
    wps
    vz
    cv
    #
    cC
    wcel
    #
    w3a
    #
    wth
    cA
    cR
    w-bnj15
    #
    @0
    cA
    wcel
    #
    wa
    #
    vw
    cv
    cA
    wcel
    #
    wa
    #
    @6
    wth
    @3
    cX
    cA
    wcel
    #
    @0
    cA
    cR
    cX
    c-bnj18
    #
    wcel
    #
    w3a
    #
    @5
    @6
    w3a
    #
    @2
    @7
    bnj1173.5
    @2
    @12
    @7
    @11
    @5
    @6
    3simpc
    @2
    @7
    @7
    @11
    wa
    #
    @12
    @2
    @3
    @8
    @10
    @7
    @13
    wi
    wph
    wps
    @3
    @1
    bnj1173.9
    3adant3
    #
    wph
    wps
    @8
    @1
    bnj1173.17
    3adant3
    @1
    wph
    @10
    wps
    @10
    @0
    @9
    cB
    cin
    #
    cC
    @0
    @15
    wcel
    @10
    @0
    cB
    wcel
    @0
    @9
    cB
    elin
    simplbi
    bnj1173.3
    eleq2s
    3ad2ant3
    #
    @11
    @7
    pm3.21
    syl3anc
    @11
    @5
    @6
    bnj170
    syl6ibr
    impbid2
    syl5bb
    @2
    @5
    @6
    @2
    @3
    @4
    @14
    @2
    vz
    @9
    cA
    cA
    cR
    cX
    bnj1147
    @16
    bnj1213
    jca
    biantrurd
    bitr4d
end
