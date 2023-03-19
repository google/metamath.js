include "eqid.mm"
include "3brtr4g.mm"

theorem syl5eqbr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume syl5eqbr.1: |- A = B
  assume syl5eqbr.2: |- ( ph -> B R C )


  assert |- ( ph -> A R C )

  proof
    wph
    cB
    cC
    cA
    cC
    cR
    syl5eqbr.2
    syl5eqbr.1
    cC
    eqid
    3brtr4g
end
