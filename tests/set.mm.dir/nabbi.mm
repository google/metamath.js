include "cab.mm"
include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "wb.mm"
include "wex.mm"
include "df-ne.mm"
include "wal.mm"
include "exnal.mm"
include "xor3.mm"
include "exbii.mm"
include "bitr3i.mm"
include "abbi.mm"
include "xchnxbi.mm"
include "bitr2i.mm"

theorem nabbi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( E. x ( ph <-> -. ps ) <-> { x | ph } =/= { x | ps } )

  proof
    wph
    vx
    cab
    #
    wps
    vx
    cab
    #
    wne
    @0
    @1
    wceq
    #
    wn
    wph
    wps
    wn
    wb
    #
    vx
    wex
    #
    @0
    @1
    df-ne
    wph
    wps
    wb
    #
    vx
    wal
    #
    @4
    @2
    @6
    wn
    @5
    wn
    #
    vx
    wex
    @4
    @5
    vx
    exnal
    @7
    @3
    vx
    wph
    wps
    xor3
    exbii
    bitr3i
    wph
    wps
    vx
    abbi
    xchnxbi
    bitr2i
end
