include "cc0.mm"
include "0red.mm"
include "ltled.mm"
include "addgegt0d.mm"

theorem addgt0d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )
  assume addgt0d.3: |- ( ph -> 0 < A )
  assume addgt0d.4: |- ( ph -> 0 < B )


  assert |- ( ph -> 0 < ( A + B ) )

  proof
    wph
    cA
    cB
    leidd.1
    ltnegd.2
    wph
    cc0
    cA
    wph
    0red
    leidd.1
    addgt0d.3
    ltled
    addgt0d.4
    addgegt0d
end
