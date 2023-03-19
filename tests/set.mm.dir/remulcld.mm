include "cr.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "remulcl.mm"
include "syl2anc.mm"

theorem remulcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume recnd.1: |- ( ph -> A e. RR )
  assume readdcld.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( A x. B ) e. RR )

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
    cmul
    co
    cr
    wcel
    recnd.1
    readdcld.2
    cA
    cB
    remulcl
    syl2anc
end
