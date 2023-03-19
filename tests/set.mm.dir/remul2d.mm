include "cr.mm"
include "wcel.mm"
include "cc.mm"
include "cmul.mm"
include "co.mm"
include "cre.mm"
include "cfv.mm"
include "wceq.mm"
include "remul2.mm"
include "syl2anc.mm"

theorem remul2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume crred.1: |- ( ph -> A e. RR )
  assume remul2d.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( Re ` ( A x. B ) ) = ( A x. ( Re ` B ) ) )

  proof
    wph
    cA
    cr
    wcel
    cB
    cc
    wcel
    cA
    cB
    cmul
    co
    cre
    cfv
    cA
    cB
    cre
    cfv
    cmul
    co
    wceq
    crred.1
    remul2d.2
    cA
    cB
    remul2
    syl2anc
end
