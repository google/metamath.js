include "ltled.mm"
include "ltleaddd.mm"

theorem lt2addd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )
  assume ltadd1d.3: |- ( ph -> C e. RR )
  assume lt2addd.4: |- ( ph -> D e. RR )
  assume lt2addd.5: |- ( ph -> A < C )
  assume lt2addd.6: |- ( ph -> B < D )


  assert |- ( ph -> ( A + B ) < ( C + D ) )

  proof
    wph
    cA
    cB
    cC
    cD
    leidd.1
    ltnegd.2
    ltadd1d.3
    lt2addd.4
    lt2addd.5
    wph
    cB
    cD
    ltnegd.2
    lt2addd.4
    lt2addd.6
    ltled
    ltleaddd
end
