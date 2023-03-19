include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "rereccl.mm"
include "syl2anc.mm"

theorem rereccld
  let wph: wff ph
  let cA: class A
  assume redivcld.1: |- ( ph -> A e. RR )
  assume rereccld.2: |- ( ph -> A =/= 0 )


  assert |- ( ph -> ( 1 / A ) e. RR )

  proof
    wph
    cA
    cr
    wcel
    cA
    cc0
    wne
    c1
    cA
    cdiv
    co
    cr
    wcel
    redivcld.1
    rereccld.2
    cA
    rereccl
    syl2anc
end
