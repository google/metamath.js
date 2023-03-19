include "wnfc.mm"
include "wrex.mm"
include "wsbc.mm"
include "wb.mm"
include "nfcv.mm"
include "sbcrext.mm"
include "ax-mp.mm"

theorem sbcrex
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z

  disjoint A y
  disjoint B x
  disjoint x y
  disjoint y z
  disjoint A z
  disjoint x z
  disjoint ph z
  disjoint B z
  assert |- ( [. A / x ]. E. y e. B ph <-> E. y e. B [. A / x ]. ph )

  proof
    vy
    cA
    wnfc
    wph
    vy
    cB
    wrex
    vx
    cA
    wsbc
    wph
    vx
    cA
    wsbc
    vy
    cB
    wrex
    wb
    vy
    cA
    nfcv
    wph
    vx
    vy
    cA
    cB
    sbcrext
    ax-mp
end
