include "wnf.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "w3a.mm"
include "wex.mm"
include "3ad2ant3.mm"
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

theorem bj-ceqsalt1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  assume bj-ceqsalt1.1: |- ( th -> E. x ch )


  assert |- ( ( F/ x ps /\ A. x ( ch -> ( ph <-> ps ) ) /\ th ) -> ( A. x ( ch -> ph ) <-> ps ) )

  proof
    wps
    vx
    wnf
    #
    wch
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
    w3a
    #
    wch
    wph
    wi
    #
    vx
    wal
    #
    wps
    @4
    @6
    wch
    vx
    wex
    #
    wps
    wth
    @0
    @7
    @3
    bj-ceqsalt1.1
    3ad2ant3
    @4
    @6
    wch
    wps
    wi
    #
    vx
    wal
    #
    @7
    wps
    wi
    #
    @3
    @0
    @6
    @9
    wi
    wth
    @2
    @5
    @8
    vx
    @1
    wph
    wps
    wch
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
    wth
    wch
    wps
    vx
    19.23t
    3ad2ant1
    sylibd
    mpid
    @4
    wps
    @5
    wi
    #
    vx
    wal
    #
    wps
    @6
    wi
    #
    @3
    @0
    @12
    wth
    @2
    @11
    vx
    @2
    wch
    wps
    wph
    @1
    wps
    wph
    wi
    wch
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
    wth
    wps
    @5
    vx
    19.21t
    3ad2ant1
    mpbid
    impbid
end
