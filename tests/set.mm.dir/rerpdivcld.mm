include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "cdiv.mm"
include "co.mm"
include "rerpdivcl.mm"
include "syl2anc.mm"

theorem rerpdivcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume rpgecld.1: |- ( ph -> A e. RR )
  assume rpgecld.2: |- ( ph -> B e. RR+ )


  assert |- ( ph -> ( A / B ) e. RR )

  proof
    wph
    cA
    cr
    wcel
    cB
    crp
    wcel
    cA
    cB
    cdiv
    co
    cr
    wcel
    rpgecld.1
    rpgecld.2
    cA
    cB
    rerpdivcl
    syl2anc
end
