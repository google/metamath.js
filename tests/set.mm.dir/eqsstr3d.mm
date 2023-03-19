include "eqcomd.mm"
include "eqsstrd.mm"

theorem eqsstr3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume eqsstr3d.1: |- ( ph -> B = A )
  assume eqsstr3d.2: |- ( ph -> B C_ C )


  assert |- ( ph -> A C_ C )

  proof
    wph
    cA
    cB
    cC
    wph
    cB
    cA
    eqsstr3d.1
    eqcomd
    eqsstr3d.2
    eqsstrd
end
