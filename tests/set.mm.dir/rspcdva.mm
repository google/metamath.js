include "wral.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "adantl.mm"
include "rspcdv.mm"
include "mpd.mm"

theorem rspcdva
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cC: class C
  assume rspcdva.1: |- ( x = C -> ( ps <-> ch ) )
  assume rspcdva.2: |- ( ph -> A. x e. A ps )
  assume rspcdva.3: |- ( ph -> C e. A )

  disjoint A x
  disjoint C x
  disjoint ch x
  disjoint ph x
  assert |- ( ph -> ch )

  proof
    wph
    wps
    vx
    cA
    wral
    wch
    rspcdva.2
    wph
    wps
    wch
    vx
    cC
    cA
    rspcdva.3
    vx
    cv
    cC
    wceq
    wps
    wch
    wb
    wph
    rspcdva.1
    adantl
    rspcdv
    mpd
end
