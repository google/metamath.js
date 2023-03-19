include "walsi.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "w3a.mm"
include "alimp-no-surprise.mm"
include "df-alsi.mm"
include "anbi12i.mm"
include "anandi3r.mm"
include "3ancomb.mm"
include "3bitr2i.mm"
include "mtbir.mm"

theorem alsi-no-surprise
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vk: setvar k


  assert |- -. ( A! x ( ph -> ps ) /\ A! x ( ph -> -. ps ) )

  proof
    wph
    wps
    vx
    walsi
    #
    wph
    wps
    wn
    #
    vx
    walsi
    #
    wa
    #
    wph
    wps
    wi
    vx
    wal
    #
    wph
    @1
    wi
    vx
    wal
    #
    wph
    vx
    wex
    #
    w3a
    #
    wph
    wps
    vx
    alimp-no-surprise
    @3
    @4
    @6
    wa
    #
    @5
    @6
    wa
    #
    wa
    @4
    @6
    @5
    w3a
    @7
    @0
    @8
    @2
    @9
    wph
    wps
    vx
    df-alsi
    wph
    @1
    vx
    df-alsi
    anbi12i
    @4
    @6
    @5
    anandi3r
    @4
    @6
    @5
    3ancomb
    3bitr2i
    mtbir
end
