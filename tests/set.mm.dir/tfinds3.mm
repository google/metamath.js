include "wi.mm"
include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "imbi2d.mm"
include "csuc.mm"
include "con0.mm"
include "wcel.mm"
include "a2d.mm"
include "wral.mm"
include "wlim.mm"
include "r19.21v.mm"
include "syl5bi.mm"
include "tfinds.mm"

theorem tfinds3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume tfinds3.1: |- ( x = (/) -> ( ph <-> ps ) )
  assume tfinds3.2: |- ( x = y -> ( ph <-> ch ) )
  assume tfinds3.3: |- ( x = suc y -> ( ph <-> th ) )
  assume tfinds3.4: |- ( x = A -> ( ph <-> ta ) )
  assume tfinds3.5: |- ( et -> ps )
  assume tfinds3.6: |- ( y e. On -> ( et -> ( ch -> th ) ) )
  assume tfinds3.7: |- ( Lim x -> ( et -> ( A. y e. x ch -> ph ) ) )

  disjoint A x
  disjoint ph y
  disjoint ch x
  disjoint ta x
  disjoint x y
  disjoint et x
  disjoint et y
  assert |- ( A e. On -> ( et -> ta ) )

  proof
    wet
    wph
    wi
    #
    wet
    wps
    wi
    wet
    wch
    wi
    #
    wet
    wth
    wi
    wet
    wta
    wi
    vx
    vy
    cA
    vx
    cv
    #
    c0
    wceq
    wph
    wps
    wet
    tfinds3.1
    imbi2d
    @2
    vy
    cv
    #
    wceq
    wph
    wch
    wet
    tfinds3.2
    imbi2d
    @2
    @3
    csuc
    wceq
    wph
    wth
    wet
    tfinds3.3
    imbi2d
    @2
    cA
    wceq
    wph
    wta
    wet
    tfinds3.4
    imbi2d
    tfinds3.5
    @3
    con0
    wcel
    wet
    wch
    wth
    tfinds3.6
    a2d
    @1
    vy
    @2
    wral
    wet
    wch
    vy
    @2
    wral
    #
    wi
    @2
    wlim
    #
    @0
    wet
    wch
    vy
    @2
    r19.21v
    @5
    wet
    @4
    wph
    tfinds3.7
    a2d
    syl5bi
    tfinds
end
