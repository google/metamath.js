include "cz.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "zaddcl.mm"
include "syl2anc.mm"

theorem zaddcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume zred.1: |- ( ph -> A e. ZZ )
  assume zaddcld.1: |- ( ph -> B e. ZZ )


  assert |- ( ph -> ( A + B ) e. ZZ )

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
    caddc
    co
    cz
    wcel
    zred.1
    zaddcld.1
    cA
    cB
    zaddcl
    syl2anc
end
