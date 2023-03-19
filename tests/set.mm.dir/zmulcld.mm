include "cz.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "zmulcl.mm"
include "syl2anc.mm"

theorem zmulcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume zred.1: |- ( ph -> A e. ZZ )
  assume zaddcld.1: |- ( ph -> B e. ZZ )


  assert |- ( ph -> ( A x. B ) e. ZZ )

  proof
    wph
    cA
    cz
    wcel
    cB
    cz
    wcel
    cA
    cB
    cmul
    co
    cz
    wcel
    zred.1
    zaddcld.1
    cA
    cB
    zmulcl
    syl2anc
end
