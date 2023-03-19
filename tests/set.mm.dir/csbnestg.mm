include "wcel.mm"
include "wnfc.mm"
include "wal.mm"
include "csb.mm"
include "wceq.mm"
include "nfcv.mm"
include "ax-gen.mm"
include "csbnestgf.mm"
include "mpan2.mm"

theorem csbnestg
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vz: setvar z
  let wph: wff ph

  disjoint C x
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint ph z
  disjoint ph x
  assert |- ( A e. V -> [_ A / x ]_ [_ B / y ]_ C = [_ [_ A / x ]_ B / y ]_ C )

  proof
    cA
    cV
    wcel
    vx
    cC
    wnfc
    #
    vy
    wal
    vx
    cA
    vy
    cB
    cC
    csb
    csb
    vy
    vx
    cA
    cB
    csb
    cC
    csb
    wceq
    @0
    vy
    vx
    cC
    nfcv
    ax-gen
    vx
    vy
    cA
    cB
    cC
    cV
    csbnestgf
    mpan2
end
