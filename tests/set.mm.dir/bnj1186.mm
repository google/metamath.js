include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wex.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "19.21v.mm"
include "exbii.mm"
include "mpbi.mm"
include "19.37iv.mm"
include "19.28v.mm"
include "sylib.mm"
include "df-ral.mm"
include "anbi2i.mm"
include "sylibr.mm"
include "df-rex.mm"

theorem bnj1186
  let wph: wff ph
  let wps: wff ps
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let cR: class R
  assume bnj1186.1: |- E. z A. w ( ( ph /\ ps ) -> ( z e. B /\ ( w e. B -> -. w R z ) ) )

  disjoint B w
  disjoint ph w
  disjoint ph z
  disjoint w z
  disjoint ps w
  disjoint ps z
  assert |- ( ( ph /\ ps ) -> E. z e. B A. w e. B -. w R z )

  proof
    wph
    wps
    wa
    #
    vz
    cv
    #
    cB
    wcel
    #
    vw
    cv
    #
    @1
    cR
    wbr
    wn
    #
    vw
    cB
    wral
    #
    wa
    #
    vz
    wex
    #
    @5
    vz
    cB
    wrex
    @0
    @2
    @3
    cB
    wcel
    @4
    wi
    #
    vw
    wal
    #
    wa
    #
    vz
    wex
    #
    @7
    @0
    @2
    @8
    wa
    #
    vw
    wal
    #
    vz
    wex
    @11
    @0
    @13
    vz
    @0
    @12
    wi
    vw
    wal
    #
    vz
    wex
    @0
    @13
    wi
    #
    vz
    wex
    bnj1186.1
    @14
    @15
    vz
    @0
    @12
    vw
    19.21v
    exbii
    mpbi
    19.37iv
    @13
    @10
    vz
    @2
    @8
    vw
    19.28v
    exbii
    sylib
    @6
    @10
    vz
    @5
    @9
    @2
    @4
    vw
    cB
    df-ral
    anbi2i
    exbii
    sylibr
    @5
    vz
    cB
    df-rex
    sylibr
end
