include "wnf.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "w3a.mm"
include "wex.mm"
include "elisset.mm"
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

theorem ceqsalt
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V

  disjoint A x
  assert |- ( ( F/ x ps /\ A. x ( x = A -> ( ph <-> ps ) ) /\ A e. V ) -> ( A. x ( x = A -> ph ) <-> ps ) )

  proof
    wps
    vx
    wnf
    #
    vx
    cv
    cA
    wceq
    #
    wph
    wps
    wb
    #
    wi
    #
    vx
    wal
    #
    cA
    cV
    wcel
    #
    w3a
    #
    @1
    wph
    wi
    #
    vx
    wal
    #
    wps
    @6
    @8
    @1
    vx
    wex
    #
    wps
    @5
    @0
    @9
    @4
    vx
    cA
    cV
    elisset
    3ad2ant3
    @6
    @8
    @1
    wps
    wi
    #
    vx
    wal
    #
    @9
    wps
    wi
    #
    @4
    @0
    @8
    @11
    wi
    @5
    @3
    @7
    @10
    vx
    @2
    wph
    wps
    @1
    wph
    wps
    biimp
    imim3i
    al2imi
    3ad2ant2
    @0
    @4
    @11
    @12
    wb
    @5
    @1
    wps
    vx
    19.23t
    3ad2ant1
    sylibd
    mpid
    @6
    wps
    @7
    wi
    #
    vx
    wal
    #
    wps
    @8
    wi
    #
    @4
    @0
    @14
    @5
    @3
    @13
    vx
    @3
    @1
    wps
    wph
    @2
    wps
    wph
    wi
    @1
    wph
    wps
    biimpr
    imim2i
    com23
    alimi
    3ad2ant2
    @0
    @4
    @14
    @15
    wb
    @5
    wps
    @7
    vx
    19.21t
    3ad2ant1
    mpbid
    impbid
end
