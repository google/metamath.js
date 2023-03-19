include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "ralrimi.mm"
include "wnf.mm"
include "wb.mm"
include "r19.23t.mm"
include "syl.mm"
include "mpbid.mm"

theorem rexlimd2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume rexlimd2.1: |- F/ x ph
  assume rexlimd2.2: |- ( ph -> F/ x ch )
  assume rexlimd2.3: |- ( ph -> ( x e. A -> ( ps -> ch ) ) )


  assert |- ( ph -> ( E. x e. A ps -> ch ) )

  proof
    wph
    wps
    wch
    wi
    #
    vx
    cA
    wral
    #
    wps
    vx
    cA
    wrex
    wch
    wi
    #
    wph
    @0
    vx
    cA
    rexlimd2.1
    rexlimd2.3
    ralrimi
    wph
    wch
    vx
    wnf
    @1
    @2
    wb
    rexlimd2.2
    wps
    wch
    vx
    cA
    r19.23t
    syl
    mpbid
end
