include "cvv.mm"
include "wcel.mm"
include "wsbc.mm"
include "wi.mm"
include "wal.mm"
include "alrimiv.mm"
include "spsbc.mm"
include "sbcim1.mm"
include "syl56.mm"
include "wn.mm"
include "sbcex.mm"
include "con3i.mm"
include "pm2.21d.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem sbcimdvOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume sbcimdv.1: |- ( ph -> ( ps -> ch ) )

  disjoint ph x
  assert |- ( ph -> ( [. A / x ]. ps -> [. A / x ]. ch ) )

  proof
    cA
    cvv
    wcel
    #
    wph
    wps
    vx
    cA
    wsbc
    #
    wch
    vx
    cA
    wsbc
    #
    wi
    #
    wi
    wph
    wps
    wch
    wi
    #
    vx
    wal
    @0
    @4
    vx
    cA
    wsbc
    @3
    wph
    @4
    vx
    sbcimdv.1
    alrimiv
    @4
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
    @0
    wn
    #
    @3
    wph
    @5
    @1
    @2
    @1
    @0
    wps
    vx
    cA
    sbcex
    con3i
    pm2.21d
    a1d
    pm2.61i
end
