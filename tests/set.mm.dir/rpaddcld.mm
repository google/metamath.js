include "crp.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "rpaddcl.mm"
include "syl2anc.mm"

theorem rpaddcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume rpred.1: |- ( ph -> A e. RR+ )
  assume rpaddcld.1: |- ( ph -> B e. RR+ )


  assert |- ( ph -> ( A + B ) e. RR+ )

  proof
    wph
    cA
    crp
    wcel
    cB
    crp
    wcel
    cA
    cB
    caddc
    co
    crp
    wcel
    rpred.1
    rpaddcld.1
    cA
    cB
    rpaddcl
    syl2anc
end
