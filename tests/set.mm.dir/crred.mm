include "cr.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cre.mm"
include "cfv.mm"
include "wceq.mm"
include "crre.mm"
include "syl2anc.mm"

theorem crred
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume crred.1: |- ( ph -> A e. RR )
  assume crred.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( Re ` ( A + ( _i x. B ) ) ) = A )

  proof
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    ci
    cB
    cmul
    co
    caddc
    co
    cre
    cfv
    cA
    wceq
    crred.1
    crred.2
    cA
    cB
    crre
    syl2anc
end
