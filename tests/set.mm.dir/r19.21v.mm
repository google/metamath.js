include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "bi2.04.mm"
include "albii.mm"
include "19.21v.mm"
include "bitri.mm"
include "df-ral.mm"
include "imbi2i.mm"
include "3bitr4i.mm"

theorem r19.21v
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param cA: class A

  disjoint ph x
  assert |- ( A. x e. A ( ph -> ps ) <-> ( ph -> A. x e. A ps ) )

  proof
    vx
    cv
    cA
    wcel
    #
    wph
    wps
    wi
    #
    wi
    #
    vx
    wal
    #
    wph
    @0
    wps
    wi
    #
    vx
    wal
    #
    wi
    #
    @1
    vx
    cA
    wral
    wph
    wps
    vx
    cA
    wral
    #
    wi
    @3
    wph
    @4
    wi
    #
    vx
    wal
    @6
    @2
    @8
    vx
    @0
    wph
    wps
    bi2.04
    albii
    wph
    @4
    vx
    19.21v
    bitri
    @1
    vx
    cA
    df-ral
    @7
    @5
    wph
    wps
    vx
    cA
    df-ral
    imbi2i
    3bitr4i
end
