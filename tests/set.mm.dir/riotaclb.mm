include "c0.mm"
include "wcel.mm"
include "wn.mm"
include "wreu.mm"
include "crio.mm"
include "riotacl.mm"
include "riotaund.mm"
include "eleq1d.mm"
include "notbid.mm"
include "biimprcd.mm"
include "con4d.mm"
include "impbid2.mm"

theorem riotaclb
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( -. (/) e. A -> ( E! x e. A ph <-> ( iota_ x e. A ph ) e. A ) )

  proof
    c0
    cA
    wcel
    #
    wn
    #
    wph
    vx
    cA
    wreu
    #
    wph
    vx
    cA
    crio
    #
    cA
    wcel
    #
    wph
    vx
    cA
    riotacl
    @1
    @2
    @4
    @2
    wn
    #
    @4
    wn
    @1
    @5
    @4
    @0
    @5
    @3
    c0
    cA
    wph
    vx
    cA
    riotaund
    eleq1d
    notbid
    biimprcd
    con4d
    impbid2
end
