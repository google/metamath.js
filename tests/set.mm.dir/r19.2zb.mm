include "c0.mm"
include "wne.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "r19.2z.mm"
include "ex.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "noel.mm"
include "pm2.21i.mm"
include "rgen.mm"
include "raleq.mm"
include "mpbiri.mm"
include "necon3bi.mm"
include "wa.mm"
include "wex.mm"
include "exsimpl.mm"
include "df-rex.mm"
include "n0.mm"
include "3imtr4i.mm"
include "ja.mm"
include "impbii.mm"

theorem r19.2zb
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A =/= (/) <-> ( A. x e. A ph -> E. x e. A ph ) )

  proof
    cA
    c0
    wne
    #
    wph
    vx
    cA
    wral
    #
    wph
    vx
    cA
    wrex
    #
    wi
    @0
    @1
    @2
    wph
    vx
    cA
    r19.2z
    ex
    @1
    @2
    @0
    @1
    cA
    c0
    cA
    c0
    wceq
    @1
    wph
    vx
    c0
    wral
    wph
    vx
    c0
    vx
    cv
    #
    c0
    wcel
    wph
    @3
    noel
    pm2.21i
    rgen
    wph
    vx
    cA
    c0
    raleq
    mpbiri
    necon3bi
    @3
    cA
    wcel
    #
    wph
    wa
    vx
    wex
    @4
    vx
    wex
    @2
    @0
    @4
    wph
    vx
    exsimpl
    wph
    vx
    cA
    df-rex
    vx
    cA
    n0
    3imtr4i
    ja
    impbii
end
