include "eqid.mm"
include "3brtr3g.mm"

theorem syl6breq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume syl6breq.1: |- ( ph -> A R B )
  assume syl6breq.2: |- B = C


  assert |- ( ph -> A R C )

  proof
    wph
    cA
    cB
    cA
    cC
    cR
    syl6breq.1
    cA
    eqid
    syl6breq.2
    3brtr3g
end
