include "cv.mm"
include "wss.mm"
include "wa.mm"
include "cleq2lem.mm"
include "cbvabv.mm"

theorem cbvcllem
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  assume cbvcllem.y: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
  disjoint X x
  disjoint X y
  disjoint ps x
  disjoint ph y
  assert |- { x | ( X C_ x /\ ph ) } = { y | ( X C_ y /\ ps ) }

  proof
    cX
    vx
    cv
    #
    wss
    wph
    wa
    cX
    vy
    cv
    #
    wss
    wps
    wa
    vx
    vy
    wph
    wps
    @0
    @1
    cX
    cbvcllem.y
    cleq2lem
    cbvabv
end
