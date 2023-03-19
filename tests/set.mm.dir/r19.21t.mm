include "wnf.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "19.21t.mm"
include "df-ral.mm"
include "bi2.04.mm"
include "albii.mm"
include "bitri.mm"
include "imbi2i.mm"
include "3bitr4g.mm"

theorem r19.21t
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( F/ x ph -> ( A. x e. A ( ph -> ps ) <-> ( ph -> A. x e. A ps ) ) )

  proof
    wph
    vx
    wnf
    wph
    vx
    cv
    cA
    wcel
    #
    wps
    wi
    #
    wi
    #
    vx
    wal
    #
    wph
    @1
    vx
    wal
    #
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
    wps
    vx
    cA
    wral
    #
    wi
    wph
    @1
    vx
    19.21t
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
    @8
    @2
    vx
    @0
    wph
    wps
    bi2.04
    albii
    bitri
    @7
    @4
    wph
    wps
    vx
    cA
    df-ral
    imbi2i
    3bitr4g
end
