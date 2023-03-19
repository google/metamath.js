include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "redivcl.mm"
include "syl3anc.mm"

theorem redivcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume redivcld.1: |- ( ph -> A e. RR )
  assume redivcld.2: |- ( ph -> B e. RR )
  assume redivcld.3: |- ( ph -> B =/= 0 )


  assert |- ( ph -> ( A / B ) e. RR )

  proof
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cB
    cc0
    wne
    cA
    cB
    cdiv
    co
    cr
    wcel
    redivcld.1
    redivcld.2
    redivcld.3
    cA
    cB
    redivcl
    syl3anc
end
