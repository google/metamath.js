include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "cab.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "nfcv.mm"
include "nfab1.mm"
include "nfel2.mm"
include "nfv.mm"
include "nfbi.mm"
include "pm5.5.mm"
include "spcgf.mm"
include "abid.mm"
include "eleq1.mm"
include "syl5bbr.mm"
include "bibi1d.mm"
include "biimpd.mm"
include "a2i.mm"
include "alimi.mm"
include "impel.mm"

theorem elabgt
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint ps x
  assert |- ( ( A e. B /\ A. x ( x = A -> ( ph <-> ps ) ) ) -> ( A e. { x | ph } <-> ps ) )

  proof
    cA
    cB
    wcel
    vx
    cv
    #
    cA
    wceq
    #
    cA
    wph
    vx
    cab
    #
    wcel
    #
    wps
    wb
    #
    wi
    #
    vx
    wal
    @4
    @1
    wph
    wps
    wb
    #
    wi
    #
    vx
    wal
    @5
    @4
    vx
    cA
    cB
    vx
    cA
    nfcv
    @3
    wps
    vx
    vx
    cA
    @2
    wph
    vx
    nfab1
    nfel2
    wps
    vx
    nfv
    nfbi
    @1
    @4
    pm5.5
    spcgf
    @7
    @5
    vx
    @1
    @6
    @4
    @1
    @6
    @4
    @1
    wph
    @3
    wps
    wph
    @0
    @2
    wcel
    @1
    @3
    wph
    vx
    abid
    @0
    cA
    @2
    eleq1
    syl5bbr
    bibi1d
    biimpd
    a2i
    alimi
    impel
end
