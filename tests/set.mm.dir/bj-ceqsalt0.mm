include "wnf.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "w3a.mm"
include "simp3.mm"
include "biimp.mm"
include "imim3i.mm"
include "al2imi.mm"
include "3ad2ant2.mm"
include "19.23t.mm"
include "3ad2ant1.mm"
include "sylibd.mm"
include "mpid.mm"
include "biimpr.mm"
include "imim2i.mm"
include "com23.mm"
include "alimi.mm"
include "19.21t.mm"
include "mpbid.mm"
include "impbid.mm"

theorem bj-ceqsalt0
  let wph: wff ph
  let wps: wff ps
  let wth: wff th
  let vx: setvar x


  assert |- ( ( F/ x ps /\ A. x ( th -> ( ph <-> ps ) ) /\ E. x th ) -> ( A. x ( th -> ph ) <-> ps ) )

  proof
    wps
    vx
    wnf
    #
    wth
    wph
    wps
    wb
    #
    wi
    #
    vx
    wal
    #
    wth
    vx
    wex
    #
    w3a
    #
    wth
    wph
    wi
    #
    vx
    wal
    #
    wps
    @5
    @7
    @4
    wps
    @0
    @3
    @4
    simp3
    @5
    @7
    wth
    wps
    wi
    #
    vx
    wal
    #
    @4
    wps
    wi
    #
    @3
    @0
    @7
    @9
    wi
    @4
    @2
    @6
    @8
    vx
    @1
    wph
    wps
    wth
    wph
    wps
    biimp
    imim3i
    al2imi
    3ad2ant2
    @0
    @3
    @9
    @10
    wb
    @4
    wth
    wps
    vx
    19.23t
    3ad2ant1
    sylibd
    mpid
    @5
    wps
    @6
    wi
    #
    vx
    wal
    #
    wps
    @7
    wi
    #
    @3
    @0
    @12
    @4
    @2
    @11
    vx
    @2
    wth
    wps
    wph
    @1
    wps
    wph
    wi
    wth
    wph
    wps
    biimpr
    imim2i
    com23
    alimi
    3ad2ant2
    @0
    @3
    @12
    @13
    wb
    @4
    wps
    @6
    vx
    19.21t
    3ad2ant1
    mpbid
    impbid
end
