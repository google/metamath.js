include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "imbi1d.mm"
include "pm5.32i.mm"
include "imbi2i.mm"
include "albii.mm"
include "exbii.mm"
include "mpbi.mm"
include "c-bnj18.mm"
include "cin.mm"
include "simp3.mm"
include "syl6eleq.mm"
include "elin2d.mm"
include "anim1i.mm"
include "imim2i.mm"
include "alimi.mm"
include "bnj101.mm"

theorem bnj1172
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
  assume bnj1172.3: |- C = ( _trCl ( X , A , R ) i^i B )
  assume bnj1172.96: |- E. z A. w ( ( ph /\ ps ) -> ( ( ph /\ ps /\ z e. C ) /\ ( th -> ( w R z -> -. w e. B ) ) ) )
  assume bnj1172.113: |- ( ( ph /\ ps /\ z e. C ) -> ( th <-> w e. A ) )


  assert |- E. z A. w ( ( ph /\ ps ) -> ( z e. B /\ ( w e. A -> ( w R z -> -. w e. B ) ) ) )

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
    w3a
    #
    vw
    cv
    #
    cA
    wcel
    #
    @4
    @1
    cR
    wbr
    @4
    cB
    wcel
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
    @0
    @1
    cB
    wcel
    #
    @7
    wa
    #
    wi
    #
    vw
    wal
    vz
    @0
    @3
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
    #
    vz
    wex
    @10
    vz
    wex
    bnj1172.96
    @17
    @10
    vz
    @16
    @9
    vw
    @15
    @8
    @0
    @3
    @14
    @7
    @3
    wth
    @5
    @6
    bnj1172.113
    imbi1d
    pm5.32i
    imbi2i
    albii
    exbii
    mpbi
    @9
    @13
    vw
    @8
    @12
    @0
    @3
    @11
    @7
    @3
    cA
    cR
    cX
    c-bnj18
    #
    cB
    @1
    @3
    @1
    cC
    @18
    cB
    cin
    wph
    wps
    @2
    simp3
    bnj1172.3
    syl6eleq
    elin2d
    anim1i
    imim2i
    alimi
    bnj101
end
