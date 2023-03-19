include "wcel.mm"
include "wnf.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "w3a.mm"
include "wsbc.mm"
include "wa.mm"
include "wex.mm"
include "sbc5.mm"
include "biimp.mm"
include "imim2i.mm"
include "impd.mm"
include "alimi.mm"
include "19.23t.mm"
include "biimpa.mm"
include "sylan2.mm"
include "3adant1.mm"
include "syl5bi.mm"
include "biimpr.mm"
include "com23.mm"
include "19.21t.mm"
include "sbc6g.mm"
include "3ad2ant1.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem sbciegft
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V

  disjoint A x
  assert |- ( ( A e. V /\ F/ x ps /\ A. x ( x = A -> ( ph <-> ps ) ) ) -> ( [. A / x ]. ph <-> ps ) )

  proof
    cA
    cV
    wcel
    #
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
    w3a
    #
    wph
    vx
    cA
    wsbc
    #
    wps
    @7
    @2
    wph
    wa
    #
    vx
    wex
    #
    @6
    wps
    wph
    vx
    cA
    sbc5
    @1
    @5
    @9
    wps
    wi
    #
    @0
    @5
    @1
    @8
    wps
    wi
    #
    vx
    wal
    #
    @10
    @4
    @11
    vx
    @4
    @2
    wph
    wps
    @3
    wph
    wps
    wi
    @2
    wph
    wps
    biimp
    imim2i
    impd
    alimi
    @1
    @12
    @10
    @8
    wps
    vx
    19.23t
    biimpa
    sylan2
    3adant1
    syl5bi
    @6
    wps
    @2
    wph
    wi
    #
    vx
    wal
    #
    @7
    @1
    @5
    wps
    @14
    wi
    #
    @0
    @5
    @1
    wps
    @13
    wi
    #
    vx
    wal
    #
    @15
    @4
    @16
    vx
    @4
    @2
    wps
    wph
    @3
    wps
    wph
    wi
    @2
    wph
    wps
    biimpr
    imim2i
    com23
    alimi
    @1
    @17
    @15
    wps
    @13
    vx
    19.21t
    biimpa
    sylan2
    3adant1
    @0
    @1
    @7
    @14
    wb
    @5
    wph
    vx
    cA
    cV
    sbc6g
    3ad2ant1
    sylibrd
    impbid
end
