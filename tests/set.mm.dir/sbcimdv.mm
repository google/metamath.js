include "wsbc.mm"
include "cvv.mm"
include "wcel.mm"
include "sbcex.mm"
include "wi.mm"
include "wal.mm"
include "alrimiv.mm"
include "spsbc.mm"
include "sbcim1.mm"
include "syl56.mm"
include "com3l.mm"
include "mpdi.mm"

theorem sbcimdv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume sbcimdv.1: |- ( ph -> ( ps -> ch ) )

  disjoint ph x
  assert |- ( ph -> ( [. A / x ]. ps -> [. A / x ]. ch ) )

  proof
    wph
    wps
    vx
    cA
    wsbc
    #
    cA
    cvv
    wcel
    #
    wch
    vx
    cA
    wsbc
    #
    wps
    vx
    cA
    sbcex
    @1
    wph
    @0
    @2
    wph
    wps
    wch
    wi
    #
    vx
    wal
    @1
    @3
    vx
    cA
    wsbc
    @0
    @2
    wi
    wph
    @3
    vx
    sbcimdv.1
    alrimiv
    @3
    vx
    cA
    cvv
    spsbc
    wps
    wch
    vx
    cA
    sbcim1
    syl56
    com3l
    mpdi
end
