include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "w-bnj17.mm"
include "wal.mm"
include "wex.mm"
include "w3a.mm"
include "c-bnj18.mm"
include "cin.mm"
include "eleq2i.mm"
include "notbii.mm"
include "wo.mm"
include "ianor.mm"
include "elin.mm"
include "pm4.62.mm"
include "3bitr4i.mm"
include "biimpi.mm"
include "impcom.mm"
include "sylan2b.mm"
include "ex.mm"
include "syl6.mm"
include "a2d.mm"
include "biantru.mm"
include "df-3an.mm"
include "3anass.mm"
include "3bitr2i.mm"
include "imbi2i.mm"
include "albii.mm"
include "exbii.mm"
include "mpbi.mm"
include "imdi.mm"
include "pm3.35.mm"
include "anim2i.mm"
include "imim2i.mm"
include "alimi.mm"
include "bnj101.mm"
include "ancl.mm"
include "bnj256.mm"
include "syl6ibr.mm"
include "df-bnj17.mm"

theorem bnj1174
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
  assume bnj1174.3: |- C = ( _trCl ( X , A , R ) i^i B )
  assume bnj1174.59: |- E. z A. w ( ( ph /\ ps ) -> ( z e. C /\ ( th -> ( w R z -> -. w e. C ) ) ) )
  assume bnj1174.74: |- ( th -> ( w R z -> w e. _trCl ( X , A , R ) ) )


  assert |- E. z A. w ( ( ph /\ ps ) -> ( ( ph /\ ps /\ z e. C ) /\ ( th -> ( w R z -> -. w e. B ) ) ) )

  proof
    wph
    wps
    wa
    #
    wph
    wps
    vz
    cv
    #
    cC
    wcel
    #
    wth
    vw
    cv
    #
    @1
    cR
    wbr
    #
    @3
    cB
    wcel
    #
    wn
    #
    wi
    #
    wi
    #
    w-bnj17
    #
    wi
    #
    vw
    wal
    #
    vz
    wex
    @0
    wph
    wps
    @2
    w3a
    @8
    wa
    #
    wi
    #
    vw
    wal
    #
    vz
    wex
    @0
    @2
    @8
    wa
    #
    wi
    #
    vw
    wal
    #
    @11
    vz
    @0
    @2
    wth
    @4
    @3
    cC
    wcel
    #
    wn
    #
    wi
    #
    wi
    #
    wth
    @20
    @7
    wi
    wi
    #
    wa
    #
    wa
    #
    wi
    #
    vw
    wal
    #
    @17
    vz
    @0
    @2
    @21
    wa
    #
    wi
    #
    vw
    wal
    #
    vz
    wex
    @26
    vz
    wex
    bnj1174.59
    @29
    @26
    vz
    @28
    @25
    vw
    @27
    @24
    @0
    @27
    @27
    @22
    wa
    @2
    @21
    @22
    w3a
    @24
    @22
    @27
    wth
    @4
    @19
    @6
    wth
    @4
    @3
    cA
    cR
    cX
    c-bnj18
    #
    wcel
    #
    @19
    @6
    wi
    bnj1174.74
    @31
    @19
    @6
    @19
    @31
    @3
    @30
    cB
    cin
    #
    wcel
    #
    wn
    #
    @6
    @18
    @33
    cC
    @32
    @3
    bnj1174.3
    eleq2i
    notbii
    @34
    @31
    @6
    @34
    @31
    @6
    wi
    #
    @31
    @5
    wa
    #
    wn
    @31
    wn
    @6
    wo
    @34
    @35
    @31
    @5
    ianor
    @33
    @36
    @3
    @30
    cB
    elin
    notbii
    @31
    @5
    pm4.62
    3bitr4i
    biimpi
    impcom
    sylan2b
    ex
    syl6
    a2d
    biantru
    @2
    @21
    @22
    df-3an
    @2
    @21
    @22
    3anass
    3bitr2i
    imbi2i
    albii
    exbii
    mpbi
    @25
    @16
    vw
    @24
    @15
    @0
    @23
    @8
    @2
    @22
    @21
    @21
    @8
    wi
    @8
    wth
    @20
    @7
    imdi
    @21
    @8
    pm3.35
    sylan2b
    anim2i
    imim2i
    alimi
    bnj101
    @16
    @10
    vw
    @16
    @0
    @0
    @15
    wa
    @9
    @0
    @15
    ancl
    wph
    wps
    @2
    @8
    bnj256
    syl6ibr
    alimi
    bnj101
    @11
    @14
    vz
    @10
    @13
    vw
    @9
    @12
    @0
    wph
    wps
    @2
    @8
    df-bnj17
    imbi2i
    albii
    exbii
    mpbi
end
