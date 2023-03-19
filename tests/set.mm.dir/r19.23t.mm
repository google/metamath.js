include "wnf.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wral.mm"
include "wrex.mm"
include "19.23t.mm"
include "df-ral.mm"
include "impexp.mm"
include "albii.mm"
include "bitr4i.mm"
include "df-rex.mm"
include "imbi1i.mm"
include "3bitr4g.mm"

theorem r19.23t
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( F/ x ps -> ( A. x e. A ( ph -> ps ) <-> ( E. x e. A ph -> ps ) ) )

  proof
    wps
    vx
    wnf
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    #
    wps
    wi
    #
    vx
    wal
    #
    @1
    vx
    wex
    #
    wps
    wi
    wph
    wps
    wi
    #
    vx
    cA
    wral
    #
    wph
    vx
    cA
    wrex
    #
    wps
    wi
    @1
    wps
    vx
    19.23t
    @6
    @0
    @5
    wi
    #
    vx
    wal
    @3
    @5
    vx
    cA
    df-ral
    @2
    @8
    vx
    @0
    wph
    wps
    impexp
    albii
    bitr4i
    @7
    @4
    wps
    wph
    vx
    cA
    df-rex
    imbi1i
    3bitr4g
end
