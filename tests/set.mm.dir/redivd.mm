include "cc.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "cre.mm"
include "cfv.mm"
include "wceq.mm"
include "rediv.mm"
include "syl3anc.mm"

theorem redivd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume crred.1: |- ( ph -> A e. RR )
  assume remul2d.2: |- ( ph -> B e. CC )
  assume redivd.2: |- ( ph -> A =/= 0 )


  assert |- ( ph -> ( Re ` ( B / A ) ) = ( ( Re ` B ) / A ) )

  proof
    wph
    cB
    cc
    wcel
    cA
    cr
    wcel
    cA
    cc0
    wne
    cB
    cA
    cdiv
    co
    cre
    cfv
    cB
    cre
    cfv
    cA
    cdiv
    co
    wceq
    remul2d.2
    crred.1
    redivd.2
    cB
    cA
    rediv
    syl3anc
end
