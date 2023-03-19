include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mulcom.mm"
include "syl2anc.mm"

theorem mulcomd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume addcld.1: |- ( ph -> A e. CC )
  assume addcld.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( A x. B ) = ( B x. A ) )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    cmul
    co
    cB
    cA
    cmul
    co
    wceq
    addcld.1
    addcld.2
    cA
    cB
    mulcom
    syl2anc
end
