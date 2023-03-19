include "wrex.mm"
include "wsb.mm"
include "nfv.mm"
include "nfs1v.mm"
include "sbequ12.mm"
include "cbvrex.mm"
include "nfsb.mm"
include "sbequ.mm"
include "bitri.mm"

theorem cbvrexsv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint A x
  disjoint ph y
  disjoint A y
  disjoint x z
  disjoint A z
  disjoint y z
  disjoint ph z
  assert |- ( E. x e. A ph <-> E. y e. A [ y / x ] ph )

  proof
    wph
    vx
    cA
    wrex
    wph
    vx
    vz
    wsb
    #
    vz
    cA
    wrex
    wph
    vx
    vy
    wsb
    #
    vy
    cA
    wrex
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
    cbvrex
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
    cbvrex
    bitri
end
