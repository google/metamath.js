include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmin.mm"
include "cmul.mm"
include "wceq.mm"
include "subrec.mm"
include "syl22anc.mm"

theorem subrecd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume subrecd.1: |- ( ph -> A e. CC )
  assume subrecd.2: |- ( ph -> B e. CC )
  assume subrecd.3: |- ( ph -> A =/= 0 )
  assume subrecd.4: |- ( ph -> B =/= 0 )


  assert |- ( ph -> ( ( 1 / A ) - ( 1 / B ) ) = ( ( B - A ) / ( A x. B ) ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    cc0
    wne
    cB
    cc
    wcel
    cB
    cc0
    wne
    c1
    cA
    cdiv
    co
    c1
    cB
    cdiv
    co
    cmin
    co
    cB
    cA
    cmin
    co
    cA
    cB
    cmul
    co
    cdiv
    co
    wceq
    subrecd.1
    subrecd.3
    subrecd.2
    subrecd.4
    cA
    cB
    subrec
    syl22anc
end
