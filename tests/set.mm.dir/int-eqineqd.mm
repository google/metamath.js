include "eqcomd.mm"
include "eqled.mm"

theorem int-eqineqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume int-eqineqd.1: |- ( ph -> B e. RR )
  assume int-eqineqd.2: |- ( ph -> A = B )


  assert |- ( ph -> B <_ A )

  proof
    wph
    cB
    cA
    int-eqineqd.1
    wph
    cA
    cB
    int-eqineqd.2
    eqcomd
    eqled
end
