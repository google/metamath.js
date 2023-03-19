include "wss.mm"
include "sseq12d.mm"
include "mpbid.mm"

theorem 3sstr3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3sstr3d.1: |- ( ph -> A C_ B )
  assume 3sstr3d.2: |- ( ph -> A = C )
  assume 3sstr3d.3: |- ( ph -> B = D )


  assert |- ( ph -> C C_ D )

  proof
    wph
    cA
    cB
    wss
    cC
    cD
    wss
    3sstr3d.1
    wph
    cA
    cC
    cB
    cD
    3sstr3d.2
    3sstr3d.3
    sseq12d
    mpbid
end
