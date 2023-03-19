include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "wb.mm"
include "mul0or.mm"
include "syl2anc.mm"

theorem mul0ord
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume msq0d.1: |- ( ph -> A e. CC )
  assume mul0ord.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( ( A x. B ) = 0 <-> ( A = 0 \/ B = 0 ) ) )

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
    cc0
    wceq
    cA
    cc0
    wceq
    cB
    cc0
    wceq
    wo
    wb
    msq0d.1
    mul0ord.2
    cA
    cB
    mul0or
    syl2anc
end
