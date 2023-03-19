include "ctcl.mm"
include "cfv.mm"
include "frege108d.mm"
include "frege114d.mm"

theorem frege111d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume frege111d.r: |- ( ph -> R e. _V )
  assume frege111d.a: |- ( ph -> A e. _V )
  assume frege111d.b: |- ( ph -> B e. _V )
  assume frege111d.c: |- ( ph -> C e. _V )
  assume frege111d.ac: |- ( ph -> ( A ( t+ ` R ) C \/ A = C ) )
  assume frege111d.cb: |- ( ph -> C R B )


  assert |- ( ph -> ( A ( t+ ` R ) B \/ A = B \/ B ( t+ ` R ) A ) )

  proof
    wph
    cA
    cB
    cR
    ctcl
    cfv
    wph
    cA
    cB
    cC
    cR
    frege111d.r
    frege111d.a
    frege111d.b
    frege111d.c
    frege111d.ac
    frege111d.cb
    frege108d
    frege114d
end
