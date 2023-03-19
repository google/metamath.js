include "cz.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "zsubcl.mm"
include "syl2anc.mm"

theorem zsubcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume zred.1: |- ( ph -> A e. ZZ )
  assume zaddcld.1: |- ( ph -> B e. ZZ )


  assert |- ( ph -> ( A - B ) e. ZZ )

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
    cmin
    co
    cz
    wcel
    zred.1
    zaddcld.1
    cA
    cB
    zsubcl
    syl2anc
end
