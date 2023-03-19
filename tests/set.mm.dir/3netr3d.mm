include "neeqtrd.mm"
include "eqnetrrd.mm"

theorem 3netr3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3netr3d.1: |- ( ph -> A =/= B )
  assume 3netr3d.2: |- ( ph -> A = C )
  assume 3netr3d.3: |- ( ph -> B = D )


  assert |- ( ph -> C =/= D )

  proof
    wph
    cA
    cC
    cD
    3netr3d.2
    wph
    cA
    cB
    cD
    3netr3d.1
    3netr3d.3
    neeqtrd
    eqnetrrd
end
