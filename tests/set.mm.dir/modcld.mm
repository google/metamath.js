include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "cmo.mm"
include "co.mm"
include "modcl.mm"
include "syl2anc.mm"

theorem modcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume modcld.1: |- ( ph -> A e. RR )
  assume modcld.2: |- ( ph -> B e. RR+ )


  assert |- ( ph -> ( A mod B ) e. RR )

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
    cmo
    co
    cr
    wcel
    modcld.1
    modcld.2
    cA
    cB
    modcl
    syl2anc
end
