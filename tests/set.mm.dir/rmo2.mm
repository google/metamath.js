include "wrmo.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wral.mm"
include "df-rmo.mm"
include "nfv.mm"
include "nfan.mm"
include "mo2.mm"
include "impexp.mm"
include "albii.mm"
include "df-ral.mm"
include "bitr4i.mm"
include "exbii.mm"
include "3bitri.mm"

theorem rmo2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume rmo2.1: |- F/ y ph

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( E* x e. A ph <-> E. y A. x e. A ( ph -> x = y ) )

  proof
    wph
    vx
    cA
    wrmo
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    #
    vx
    wmo
    @1
    vx
    vy
    weq
    #
    wi
    #
    vx
    wal
    #
    vy
    wex
    wph
    @2
    wi
    #
    vx
    cA
    wral
    #
    vy
    wex
    wph
    vx
    cA
    df-rmo
    @1
    vx
    vy
    @0
    wph
    vy
    @0
    vy
    nfv
    rmo2.1
    nfan
    mo2
    @4
    @6
    vy
    @4
    @0
    @5
    wi
    #
    vx
    wal
    @6
    @3
    @7
    vx
    @0
    wph
    @2
    impexp
    albii
    @5
    vx
    cA
    df-ral
    bitr4i
    exbii
    3bitri
end
