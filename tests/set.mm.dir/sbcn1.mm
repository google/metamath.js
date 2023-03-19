include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "wsbc.mm"
include "sbcex.mm"
include "sbcng.mm"
include "biimpd.mm"
include "mpcom.mm"

theorem sbcn1
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( [. A / x ]. -. ph -> -. [. A / x ]. ph )

  proof
    cA
    cvv
    wcel
    #
    wph
    wn
    #
    vx
    cA
    wsbc
    #
    wph
    vx
    cA
    wsbc
    wn
    #
    @1
    vx
    cA
    sbcex
    @0
    @2
    @3
    wph
    vx
    cA
    cvv
    sbcng
    biimpd
    mpcom
end
