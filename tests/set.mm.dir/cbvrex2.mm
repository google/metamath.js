include "wrex.mm"
include "nfcv.mm"
include "nfrex.mm"
include "weq.mm"
include "rexbidv.mm"
include "cbvrex.mm"
include "rexbii.mm"
include "bitri.mm"

theorem cbvrex2
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
  assert |- ( E. x e. A E. y e. B ph <-> E. z e. A E. w e. B ps )

  proof
    wph
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    wch
    vy
    cB
    wrex
    #
    vz
    cA
    wrex
    wps
    vw
    cB
    wrex
    #
    vz
    cA
    wrex
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
    nfrex
    wch
    vx
    vy
    cB
    vx
    cB
    nfcv
    cbvral2.2
    nfrex
    vx
    vz
    weq
    wph
    wch
    vy
    cB
    cbvral2.5
    rexbidv
    cbvrex
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
    cbvrex
    rexbii
    bitri
end
