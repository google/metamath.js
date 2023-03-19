include "eqid.mm"
include "3brtr3g.mm"

theorem syl5eqbrr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume syl5eqbrr.1: |- B = A
  assume syl5eqbrr.2: |- ( ph -> B R C )


  assert |- ( ph -> A R C )

  proof
    wph
    cB
    cC
    cA
    cC
    cR
    syl5eqbrr.2
    syl5eqbrr.1
    cC
    eqid
    3brtr3g
end
