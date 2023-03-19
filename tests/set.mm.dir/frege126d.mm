include "ctcl.mm"
include "cfv.mm"
include "frege124d.mm"
include "frege114d.mm"

theorem frege126d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  assume frege126d.f: |- ( ph -> F e. _V )
  assume frege126d.x: |- ( ph -> X e. dom F )
  assume frege126d.a: |- ( ph -> A = ( F ` X ) )
  assume frege126d.xb: |- ( ph -> X ( t+ ` F ) B )
  assume frege126d.fun: |- ( ph -> Fun F )


  assert |- ( ph -> ( A ( t+ ` F ) B \/ A = B \/ B ( t+ ` F ) A ) )

  proof
    wph
    cA
    cB
    cF
    ctcl
    cfv
    wph
    cA
    cB
    cF
    cX
    frege126d.f
    frege126d.x
    frege126d.a
    frege126d.xb
    frege126d.fun
    frege124d
    frege114d
end
