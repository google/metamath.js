include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "sseld.mm"
include "pm4.71rd.mm"
include "imbi1d.mm"
include "impexp.mm"
include "syl6bb.mm"
include "con2b.mm"
include "imbi2i.mm"
include "syl6bbr.mm"
include "anbi2d.mm"
include "pm5.74i.mm"
include "albii.mm"
include "exbii.mm"
include "mpbir.mm"

theorem bnj1171
  let wph: wff ph
  let wps: wff ps
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cR: class R
  assume bnj1171.13: |- ( ( ph /\ ps ) -> B C_ A )
  assume bnj1171.129: |- E. z A. w ( ( ph /\ ps ) -> ( z e. B /\ ( w e. A -> ( w R z -> -. w e. B ) ) ) )


  assert |- E. z A. w ( ( ph /\ ps ) -> ( z e. B /\ ( w e. B -> -. w R z ) ) )

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
    cB
    wcel
    #
    @3
    @1
    cR
    wbr
    #
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
    @0
    @2
    @3
    cA
    wcel
    #
    @5
    @4
    wn
    wi
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
    bnj1171.129
    @10
    @16
    vz
    @9
    @15
    vw
    @0
    @8
    @14
    @0
    @7
    @13
    @2
    @0
    @7
    @11
    @7
    wi
    #
    @13
    @0
    @7
    @11
    @4
    wa
    #
    @6
    wi
    @17
    @0
    @4
    @18
    @6
    @0
    @4
    @11
    @0
    cB
    cA
    @3
    bnj1171.13
    sseld
    pm4.71rd
    imbi1d
    @11
    @4
    @6
    impexp
    syl6bb
    @12
    @7
    @11
    @5
    @4
    con2b
    imbi2i
    syl6bbr
    anbi2d
    pm5.74i
    albii
    exbii
    mpbir
end
