include "wcel.mm"
include "wi.mm"
include "wsbc.mm"
include "wb.mm"
include "sbcimg.mm"
include "biimpd.mm"
include "imbi2.mm"
include "biimpcd.mm"
include "syl6ci.mm"
include "idd.mm"
include "biimpr.mm"
include "ee13.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem sbcim2g
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ( [. A / x ]. ( ph -> ( ps -> ch ) ) <-> ( [. A / x ]. ph -> ( [. A / x ]. ps -> [. A / x ]. ch ) ) ) )

  proof
    cA
    cV
    wcel
    #
    wph
    wps
    wch
    wi
    #
    wi
    vx
    cA
    wsbc
    #
    wph
    vx
    cA
    wsbc
    #
    wps
    vx
    cA
    wsbc
    wch
    vx
    cA
    wsbc
    wi
    #
    wi
    #
    @0
    @2
    @3
    @1
    vx
    cA
    wsbc
    #
    wi
    #
    @6
    @4
    wb
    #
    @5
    @0
    @2
    @7
    wph
    @1
    vx
    cA
    cV
    sbcimg
    #
    biimpd
    wps
    wch
    vx
    cA
    cV
    sbcimg
    #
    @8
    @7
    @5
    @6
    @4
    @3
    imbi2
    biimpcd
    syl6ci
    @0
    @5
    @7
    @2
    @0
    @8
    @5
    @3
    @4
    @6
    @10
    @0
    @5
    idd
    @6
    @4
    biimpr
    ee13
    @9
    sylibrd
    impbid
end
