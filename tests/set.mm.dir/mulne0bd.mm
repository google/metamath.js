include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "wb.mm"
include "mulne0b.mm"
include "syl2anc.mm"

theorem mulne0bd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume msq0d.1: |- ( ph -> A e. CC )
  assume mul0ord.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( ( A =/= 0 /\ B =/= 0 ) <-> ( A x. B ) =/= 0 ) )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cc0
    wne
    cB
    cc0
    wne
    wa
    cA
    cB
    cmul
    co
    cc0
    wne
    wb
    msq0d.1
    mul0ord.2
    cA
    cB
    mulne0b
    syl2anc
end
