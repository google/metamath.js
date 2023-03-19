include "weq.mm"
include "wal.mm"
include "wi.mm"
include "wa.mm"
include "wex.mm"
include "wsb.mm"
include "wb.mm"
include "equequ1.mm"
include "sps.mm"
include "imbi1d.mm"
include "anbi1d.mm"
include "drex1.mm"
include "anbi12d.mm"
include "df-sb.mm"
include "3bitr4g.mm"

theorem drsb1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. x x = y -> ( [ z / x ] ph <-> [ z / y ] ph ) )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    #
    vx
    vz
    weq
    #
    wph
    wi
    #
    @2
    wph
    wa
    #
    vx
    wex
    #
    wa
    vy
    vz
    weq
    #
    wph
    wi
    #
    @6
    wph
    wa
    #
    vy
    wex
    #
    wa
    wph
    vx
    vz
    wsb
    wph
    vy
    vz
    wsb
    @1
    @3
    @7
    @5
    @9
    @1
    @2
    @6
    wph
    @0
    @2
    @6
    wb
    vx
    vx
    vy
    vz
    equequ1
    sps
    #
    imbi1d
    @4
    @8
    vx
    vy
    @1
    @2
    @6
    wph
    @10
    anbi1d
    drex1
    anbi12d
    wph
    vx
    vz
    df-sb
    wph
    vy
    vz
    df-sb
    3bitr4g
end
