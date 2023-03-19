include "wral.mm"
include "wsb.mm"
include "nfv.mm"
include "nfs1v.mm"
include "sbequ12.mm"
include "cbvral.mm"
include "nfsb.mm"
include "sbequ.mm"
include "bitri.mm"

theorem cbvralsv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint ph y
  disjoint x z
  disjoint A z
  disjoint y z
  disjoint ph z
  assert |- ( A. x e. A ph <-> A. y e. A [ y / x ] ph )

  proof
    wph
    vx
    cA
    wral
    wph
    vx
    vz
    wsb
    #
    vz
    cA
    wral
    wph
    vx
    vy
    wsb
    #
    vy
    cA
    wral
    wph
    @0
    vx
    vz
    cA
    wph
    vz
    nfv
    wph
    vx
    vz
    nfs1v
    wph
    vx
    vz
    sbequ12
    cbvral
    @0
    @1
    vz
    vy
    cA
    wph
    vx
    vz
    vy
    wph
    vy
    nfv
    nfsb
    @1
    vz
    nfv
    wph
    vz
    vy
    vx
    sbequ
    cbvral
    bitri
end
