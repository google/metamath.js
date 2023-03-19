include "wfr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "w-bnj15.mm"
include "w-bnj13.mm"
include "df-bnj15.mm"
include "simplbi.mm"
include "syl.mm"
include "c-bnj18.mm"
include "cin.mm"
include "bnj1147.mm"
include "ssinss1.mm"
include "ax-mp.mm"
include "eqsstri.mm"
include "a1i.mm"
include "cv.mm"
include "c-bnj14.mm"
include "bnj906.mm"
include "syl2anc.mm"
include "ssrin.mm"
include "wbr.mm"
include "simp2bi.mm"
include "adantl.mm"
include "sseldd.mm"
include "simp3bi.mm"
include "bnj1152.mm"
include "sylanbrc.mm"
include "elind.mm"
include "ne0i.mm"
include "neeq1i.mm"
include "sylibr.mm"
include "bnj893.mm"
include "inex1g.mm"
include "syl5eqel.mm"
include "bnj951.mm"

theorem bnj1177
  let wph: wff ph
  let wps: wff ps
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cX: class X
  assume bnj1177.2: |- ( ps <-> ( X e. B /\ y e. B /\ y R X ) )
  assume bnj1177.3: |- C = ( _trCl ( X , A , R ) i^i B )
  assume bnj1177.9: |- ( ( ph /\ ps ) -> R _FrSe A )
  assume bnj1177.13: |- ( ( ph /\ ps ) -> B C_ A )
  assume bnj1177.17: |- ( ( ph /\ ps ) -> X e. A )


  assert |- ( ( ph /\ ps ) -> ( R Fr A /\ C C_ A /\ C =/= (/) /\ C e. _V ) )

  proof
    cA
    cR
    wfr
    #
    cC
    cA
    wss
    #
    cC
    c0
    wne
    #
    cC
    cvv
    wcel
    #
    wph
    wps
    wa
    #
    @4
    cA
    cR
    w-bnj15
    #
    @0
    bnj1177.9
    @5
    @0
    cA
    cR
    w-bnj13
    cA
    cR
    df-bnj15
    simplbi
    syl
    @1
    @4
    cC
    cA
    cR
    cX
    c-bnj18
    #
    cB
    cin
    #
    cA
    bnj1177.3
    @6
    cA
    wss
    @7
    cA
    wss
    cA
    cR
    cX
    bnj1147
    @6
    cB
    cA
    ssinss1
    ax-mp
    eqsstri
    a1i
    @4
    @7
    c0
    wne
    #
    @2
    @4
    vy
    cv
    #
    @7
    wcel
    @8
    @4
    cA
    cR
    cX
    c-bnj14
    #
    cB
    cin
    #
    @7
    @9
    @4
    @10
    @6
    wss
    #
    @11
    @7
    wss
    @4
    @5
    cX
    cA
    wcel
    #
    @12
    bnj1177.9
    bnj1177.17
    cA
    cR
    cX
    bnj906
    syl2anc
    @10
    @6
    cB
    ssrin
    syl
    @4
    @10
    cB
    @9
    @4
    @9
    cA
    wcel
    @9
    cX
    cR
    wbr
    #
    @9
    @10
    wcel
    @4
    cB
    cA
    @9
    bnj1177.13
    wps
    @9
    cB
    wcel
    #
    wph
    wps
    cX
    cB
    wcel
    #
    @15
    @14
    bnj1177.2
    simp2bi
    adantl
    #
    sseldd
    wps
    @14
    wph
    wps
    @16
    @15
    @14
    bnj1177.2
    simp3bi
    adantl
    cA
    cR
    cX
    @9
    bnj1152
    sylanbrc
    @17
    elind
    sseldd
    @7
    @9
    ne0i
    syl
    cC
    @7
    c0
    bnj1177.3
    neeq1i
    sylibr
    @4
    @6
    cvv
    wcel
    #
    @3
    @4
    @5
    @13
    @18
    bnj1177.9
    bnj1177.17
    cA
    cR
    cX
    bnj893
    syl2anc
    @18
    cC
    @7
    cvv
    bnj1177.3
    @6
    cB
    cvv
    inex1g
    syl5eqel
    syl
    bnj951
end
