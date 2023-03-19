include "wss.mm"
include "cres.mm"
include "wceq.mm"
include "resabs1.mm"
include "syl.mm"

theorem resabs1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume resabs1d.b: |- ( ph -> B C_ C )


  assert |- ( ph -> ( ( A |` C ) |` B ) = ( A |` B ) )

  proof
    wph
    cB
    cC
    wss
    cA
    cC
    cres
    cB
    cres
    cA
    cB
    cres
    wceq
    resabs1d.b
    cA
    cB
    cC
    resabs1
    syl
end
