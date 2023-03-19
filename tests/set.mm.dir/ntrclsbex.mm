include "cfv.mm"
include "wceq.mm"
include "a1i.mm"
include "brfvimex.mm"

theorem ntrclsbex
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cI: class I
  let cK: class K
  let cO: class O
  assume ntrclsbex.d: |- D = ( O ` B )
  assume ntrclsbex.r: |- ( ph -> I D K )


  assert |- ( ph -> B e. _V )

  proof
    wph
    cI
    cK
    cB
    cD
    cO
    ntrclsbex.r
    cD
    cB
    cO
    cfv
    wceq
    wph
    ntrclsbex.d
    a1i
    brfvimex
end
