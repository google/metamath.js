include "cr.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cim.mm"
include "cfv.mm"
include "wceq.mm"
include "crim.mm"
include "syl2anc.mm"

theorem crimd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume crred.1: |- ( ph -> A e. RR )
  assume crred.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( Im ` ( A + ( _i x. B ) ) ) = B )

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
    cim
    cfv
    cB
    wceq
    crred.1
    crred.2
    cA
    cB
    crim
    syl2anc
end
