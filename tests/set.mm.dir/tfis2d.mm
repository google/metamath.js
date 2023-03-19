include "cv.mm"
include "con0.mm"
include "wcel.mm"
include "wi.mm"
include "weq.mm"
include "wb.mm"
include "com12.mm"
include "pm5.74d.mm"
include "wral.mm"
include "r19.21v.mm"
include "a2d.mm"
include "syl5bi.mm"
include "tfis2.mm"

theorem tfis2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume tfis2d.1: |- ( ph -> ( x = y -> ( ps <-> ch ) ) )
  assume tfis2d.2: |- ( ph -> ( x e. On -> ( A. y e. x ch -> ps ) ) )

  disjoint ph x
  disjoint ph y
  disjoint x y
  disjoint ch x
  disjoint ps y
  disjoint k x
  assert |- ( ph -> ( x e. On -> ps ) )

  proof
    vx
    cv
    #
    con0
    wcel
    #
    wph
    wps
    wph
    wps
    wi
    #
    wph
    wch
    wi
    #
    vx
    vy
    vx
    vy
    weq
    #
    wph
    wps
    wch
    wph
    @4
    wps
    wch
    wb
    tfis2d.1
    com12
    pm5.74d
    @3
    vy
    @0
    wral
    wph
    wch
    vy
    @0
    wral
    #
    wi
    @1
    @2
    wph
    wch
    vy
    @0
    r19.21v
    @1
    wph
    @5
    wps
    wph
    @1
    @5
    wps
    wi
    tfis2d.2
    com12
    a2d
    syl5bi
    tfis2
    com12
end
