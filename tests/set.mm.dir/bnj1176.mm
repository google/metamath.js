include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wrex.mm"
include "wral.mm"
include "wfr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cvv.mm"
include "w-bnj17.mm"
include "syl.mm"
include "df-ral.mm"
include "rexbii.mm"
include "sylib.mm"
include "df-rex.mm"
include "19.28v.mm"
include "exbii.mm"
include "sylibr.mm"
include "19.37v.mm"
include "mpbir.mm"
include "19.21v.mm"
include "con2b.mm"
include "anbi2i.mm"
include "imbi2i.mm"
include "albii.mm"
include "mpbi.mm"
include "ax-1.mm"
include "anim2i.mm"
include "imim2i.mm"
include "alimi.mm"
include "bnj101.mm"

theorem bnj1176
  let wph: wff ph
  let wps: wff ps
  let wth: wff th
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cC: class C
  let cR: class R
  assume bnj1176.51: |- ( ( ph /\ ps ) -> ( R Fr A /\ C C_ A /\ C =/= (/) /\ C e. _V ) )
  assume bnj1176.52: |- ( ( R Fr A /\ C C_ A /\ C =/= (/) /\ C e. _V ) -> E. z e. C A. w e. C -. w R z )

  disjoint C w
  disjoint ph w
  disjoint ph z
  disjoint w z
  disjoint ps w
  disjoint ps z
  assert |- E. z A. w ( ( ph /\ ps ) -> ( z e. C /\ ( th -> ( w R z -> -. w e. C ) ) ) )

  proof
    wph
    wps
    wa
    #
    vz
    cv
    #
    cC
    wcel
    #
    vw
    cv
    #
    @1
    cR
    wbr
    #
    @3
    cC
    wcel
    #
    wn
    wi
    #
    wa
    #
    wi
    #
    vw
    wal
    #
    @0
    @2
    wth
    @6
    wi
    #
    wa
    #
    wi
    #
    vw
    wal
    vz
    @0
    @2
    @5
    @4
    wn
    #
    wi
    #
    wa
    #
    wi
    #
    vw
    wal
    #
    vz
    wex
    #
    @9
    vz
    wex
    @18
    @0
    @15
    vw
    wal
    #
    wi
    #
    vz
    wex
    #
    @21
    @0
    @19
    vz
    wex
    #
    wi
    @0
    @2
    @14
    vw
    wal
    #
    wa
    #
    vz
    wex
    #
    @22
    @0
    @23
    vz
    cC
    wrex
    #
    @25
    @0
    @13
    vw
    cC
    wral
    #
    vz
    cC
    wrex
    #
    @26
    @0
    cA
    cR
    wfr
    cC
    cA
    wss
    cC
    c0
    wne
    cC
    cvv
    wcel
    w-bnj17
    @28
    bnj1176.51
    bnj1176.52
    syl
    @27
    @23
    vz
    cC
    @13
    vw
    cC
    df-ral
    rexbii
    sylib
    @23
    vz
    cC
    df-rex
    sylib
    @19
    @24
    vz
    @2
    @14
    vw
    19.28v
    exbii
    sylibr
    @0
    @19
    vz
    19.37v
    mpbir
    @17
    @20
    vz
    @0
    @15
    vw
    19.21v
    exbii
    mpbir
    @17
    @9
    vz
    @16
    @8
    vw
    @15
    @7
    @0
    @14
    @6
    @2
    @5
    @4
    con2b
    anbi2i
    imbi2i
    albii
    exbii
    mpbi
    @8
    @12
    vw
    @7
    @11
    @0
    @6
    @10
    @2
    @6
    wth
    ax-1
    anim2i
    imim2i
    alimi
    bnj101
end
