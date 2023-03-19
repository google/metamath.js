include "cif.mm"
include "wceq.mm"
include "iftrue.mm"
include "ax-mp.mm"

theorem iftruei
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume iftruei.1: |- ph


  assert |- if ( ph , A , B ) = A

  proof
    wph
    wph
    cA
    cB
    cif
    cA
    wceq
    iftruei.1
    wph
    cA
    cB
    iftrue
    ax-mp
end
