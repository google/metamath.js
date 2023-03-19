include "wcel.mm"
include "wnf.mm"
include "wal.mm"
include "wsbc.mm"
include "csb.mm"
include "wb.mm"
include "nfv.mm"
include "ax-gen.mm"
include "sbcnestgf.mm"
include "mpan2.mm"

theorem sbcnestg
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let vz: setvar z
  let cC: class C

  disjoint ph x
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint ph z
  assert |- ( A e. V -> ( [. A / x ]. [. B / y ]. ph <-> [. [_ A / x ]_ B / y ]. ph ) )

  proof
    cA
    cV
    wcel
    wph
    vx
    wnf
    #
    vy
    wal
    wph
    vy
    cB
    wsbc
    vx
    cA
    wsbc
    wph
    vy
    vx
    cA
    cB
    csb
    wsbc
    wb
    @0
    vy
    wph
    vx
    nfv
    ax-gen
    wph
    vx
    vy
    cA
    cB
    cV
    sbcnestgf
    mpan2
end
