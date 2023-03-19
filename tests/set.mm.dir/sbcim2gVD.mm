include "wcel.mm"
include "wi.mm"
include "wsbc.mm"
include "wb.mm"
include "idn1.mm"
include "idn2.mm"
include "sbcimg.mm"
include "biimpd.mm"
include "e12.mm"
include "e1a.mm"
include "imbi2.mm"
include "biimpcd.mm"
include "e21.mm"
include "in2.mm"
include "biimpr.mm"
include "imim2d.mm"
include "com12.mm"
include "impbi.mm"
include "e11.mm"
include "in1.mm"

theorem sbcim2gVD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B


  assert |- ( A e. B -> ( [. A / x ]. ( ph -> ( ps -> ch ) ) <-> ( [. A / x ]. ph -> ( [. A / x ]. ps -> [. A / x ]. ch ) ) ) )

  proof
    cA
    cB
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
    wb
    #
    @0
    @2
    @5
    wi
    @5
    @2
    wi
    @6
    @0
    @2
    @5
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
    @7
    @4
    wb
    #
    @5
    @0
    @0
    @2
    @2
    @8
    @0
    idn1
    #
    @0
    @2
    idn2
    @0
    @2
    @8
    wph
    @1
    vx
    cA
    cB
    sbcimg
    #
    biimpd
    e12
    @0
    @0
    @9
    @10
    wps
    wch
    vx
    cA
    cB
    sbcimg
    e1a
    #
    @9
    @8
    @5
    @7
    @4
    @3
    imbi2
    biimpcd
    e21
    in2
    @0
    @5
    @2
    @0
    @5
    @8
    @2
    @8
    wb
    #
    @2
    @0
    @9
    @5
    @5
    @8
    @12
    @0
    @5
    idn2
    @9
    @4
    @7
    @3
    @7
    @4
    biimpr
    imim2d
    e12
    @0
    @0
    @13
    @10
    @11
    e1a
    @13
    @8
    @2
    @2
    @8
    biimpr
    com12
    e21
    in2
    @2
    @5
    impbi
    e11
    in1
end
