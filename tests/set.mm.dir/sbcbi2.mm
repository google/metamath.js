include "wb.mm"
include "wal.mm"
include "cab.mm"
include "wcel.mm"
include "wsbc.mm"
include "wceq.mm"
include "abbi.mm"
include "eleq2.mm"
include "sylbi.mm"
include "df-sbc.mm"
include "3bitr4g.mm"

theorem sbcbi2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( A. x ( ph <-> ps ) -> ( [. A / x ]. ph <-> [. A / x ]. ps ) )

  proof
    wph
    wps
    wb
    vx
    wal
    #
    cA
    wph
    vx
    cab
    #
    wcel
    #
    cA
    wps
    vx
    cab
    #
    wcel
    #
    wph
    vx
    cA
    wsbc
    wps
    vx
    cA
    wsbc
    @0
    @1
    @3
    wceq
    @2
    @4
    wb
    wph
    wps
    vx
    abbi
    @1
    @3
    cA
    eleq2
    sylbi
    wph
    vx
    cA
    df-sbc
    wps
    vx
    cA
    df-sbc
    3bitr4g
end
