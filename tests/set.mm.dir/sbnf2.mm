include "wnf.mm"
include "wa.mm"
include "wsb.mm"
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "wex.mm"
include "nfv.mm"
include "sb8e.mm"
include "sb8.mm"
include "imbi12i.mm"
include "df-nf.mm"
include "pm11.53v.mm"
include "3bitr4i.mm"
include "bitr4i.mm"
include "alcom.mm"
include "3bitri.mm"
include "anbi12i.mm"
include "pm4.24.mm"
include "2albiim.mm"

theorem sbnf2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph y
  disjoint ph z
  assert |- ( F/ x ph <-> A. y A. z ( [ y / x ] ph <-> [ z / x ] ph ) )

  proof
    wph
    vx
    wnf
    #
    @0
    wa
    wph
    vx
    vy
    wsb
    #
    wph
    vx
    vz
    wsb
    #
    wi
    vz
    wal
    vy
    wal
    #
    @2
    @1
    wi
    #
    vz
    wal
    vy
    wal
    #
    wa
    @0
    @1
    @2
    wb
    vz
    wal
    vy
    wal
    @0
    @3
    @0
    @5
    wph
    vx
    wex
    #
    wph
    vx
    wal
    #
    wi
    #
    @1
    vy
    wex
    #
    @2
    vz
    wal
    #
    wi
    @0
    @3
    @6
    @9
    @7
    @10
    wph
    vx
    vy
    wph
    vy
    nfv
    #
    sb8e
    wph
    vx
    vz
    wph
    vz
    nfv
    #
    sb8
    imbi12i
    wph
    vx
    df-nf
    #
    @1
    @2
    vy
    vz
    pm11.53v
    3bitr4i
    @0
    @8
    @4
    vy
    wal
    vz
    wal
    #
    @5
    @13
    @8
    @2
    vz
    wex
    #
    @1
    vy
    wal
    #
    wi
    @14
    @6
    @15
    @7
    @16
    wph
    vx
    vz
    @12
    sb8e
    wph
    vx
    vy
    @11
    sb8
    imbi12i
    @2
    @1
    vz
    vy
    pm11.53v
    bitr4i
    @4
    vz
    vy
    alcom
    3bitri
    anbi12i
    @0
    pm4.24
    @1
    @2
    vy
    vz
    2albiim
    3bitr4i
end
