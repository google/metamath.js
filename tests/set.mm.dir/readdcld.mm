include "cr.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "readdcl.mm"
include "syl2anc.mm"

theorem readdcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume recnd.1: |- ( ph -> A e. RR )
  assume readdcld.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( A + B ) e. RR )

  proof
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    caddc
    co
    cr
    wcel
    recnd.1
    readdcld.2
    cA
    cB
    readdcl
    syl2anc
end
