include "wss.mm"
include "sseq12d.mm"
include "mpbird.mm"

theorem 3sstr4d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3sstr4d.1: |- ( ph -> A C_ B )
  assume 3sstr4d.2: |- ( ph -> C = A )
  assume 3sstr4d.3: |- ( ph -> D = B )


  assert |- ( ph -> C C_ D )

  proof
    wph
    cC
    cD
    wss
    cA
    cB
    wss
    3sstr4d.1
    wph
    cC
    cA
    cD
    cB
    3sstr4d.2
    3sstr4d.3
    sseq12d
    mpbird
end
