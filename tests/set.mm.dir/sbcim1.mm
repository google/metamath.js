include "cvv.mm"
include "wcel.mm"
include "wi.mm"
include "wsbc.mm"
include "sbcex.mm"
include "sbcimg.mm"
include "biimpd.mm"
include "mpcom.mm"

theorem sbcim1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( [. A / x ]. ( ph -> ps ) -> ( [. A / x ]. ph -> [. A / x ]. ps ) )

  proof
    cA
    cvv
    wcel
    #
    wph
    wps
    wi
    #
    vx
    cA
    wsbc
    #
    wph
    vx
    cA
    wsbc
    wps
    vx
    cA
    wsbc
    wi
    #
    @1
    vx
    cA
    sbcex
    @0
    @2
    @3
    wph
    wps
    vx
    cA
    cvv
    sbcimg
    biimpd
    mpcom
end
