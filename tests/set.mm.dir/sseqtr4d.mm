include "eqcomd.mm"
include "sseqtrd.mm"

theorem sseqtr4d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume sseqtr4d.1: |- ( ph -> A C_ B )
  assume sseqtr4d.2: |- ( ph -> C = B )


  assert |- ( ph -> A C_ C )

  proof
    wph
    cA
    cB
    cC
    sseqtr4d.1
    wph
    cC
    cB
    sseqtr4d.2
    eqcomd
    sseqtrd
end
