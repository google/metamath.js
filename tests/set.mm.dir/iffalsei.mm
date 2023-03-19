include "wn.mm"
include "cif.mm"
include "wceq.mm"
include "iffalse.mm"
include "ax-mp.mm"

theorem iffalsei
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume iffalsei.1: |- -. ph


  assert |- if ( ph , A , B ) = B

  proof
    wph
    wn
    wph
    cA
    cB
    cif
    cB
    wceq
    iffalsei.1
    wph
    cA
    cB
    iffalse
    ax-mp
end
