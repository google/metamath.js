include "wceq.mm"
include "ctcl.mm"
include "cfv.mm"
include "wbr.mm"
include "eqtr4d.mm"
include "olcd.mm"

theorem frege122d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  assume frege122d.a: |- ( ph -> A = ( F ` X ) )
  assume frege122d.b: |- ( ph -> B = ( F ` X ) )


  assert |- ( ph -> ( A ( t+ ` F ) B \/ A = B ) )

  proof
    wph
    cA
    cB
    wceq
    cA
    cB
    cF
    ctcl
    cfv
    wbr
    wph
    cA
    cX
    cF
    cfv
    cB
    frege122d.a
    frege122d.b
    eqtr4d
    olcd
end
