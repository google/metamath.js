include "wss.mm"
include "cres.mm"
include "wceq.mm"
include "resabs2.mm"
include "syl.mm"

theorem resabs2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume resabs2d.1: |- ( ph -> B C_ C )


  assert |- ( ph -> ( ( A |` B ) |` C ) = ( A |` B ) )

  proof
    wph
    cB
    cC
    wss
    cA
    cB
    cres
    #
    cC
    cres
    @0
    wceq
    resabs2d.1
    cA
    cB
    cC
    resabs2
    syl
end
