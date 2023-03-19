include "wral.mm"
include "nfcv.mm"
include "nfral.mm"
include "weq.mm"
include "ralbidv.mm"
include "cbvral.mm"
include "ralbii.mm"
include "bitri.mm"

theorem cbvral2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let vk: setvar k
  assume cbvral2.1: |- F/ z ph
  assume cbvral2.2: |- F/ x ch
  assume cbvral2.3: |- F/ w ch
  assume cbvral2.4: |- F/ y ps
  assume cbvral2.5: |- ( x = z -> ( ph <-> ch ) )
  assume cbvral2.6: |- ( y = w -> ( ch <-> ps ) )

  disjoint A x
  disjoint A z
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint y z
  disjoint B z
  disjoint B w
  disjoint k x
  assert |- ( A. x e. A A. y e. B ph <-> A. z e. A A. w e. B ps )

  proof
    wph
    vy
    cB
    wral
    #
    vx
    cA
    wral
    wch
    vy
    cB
    wral
    #
    vz
    cA
    wral
    wps
    vw
    cB
    wral
    #
    vz
    cA
    wral
    @0
    @1
    vx
    vz
    cA
    wph
    vz
    vy
    cB
    vz
    cB
    nfcv
    cbvral2.1
    nfral
    wch
    vx
    vy
    cB
    vx
    cB
    nfcv
    cbvral2.2
    nfral
    vx
    vz
    weq
    wph
    wch
    vy
    cB
    cbvral2.5
    ralbidv
    cbvral
    @1
    @2
    vz
    cA
    wch
    wps
    vy
    vw
    cB
    cbvral2.3
    cbvral2.4
    cbvral2.6
    cbvral
    ralbii
    bitri
end
