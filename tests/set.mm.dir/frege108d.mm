include "ctcl.mm"
include "cfv.mm"
include "frege102d.mm"
include "frege106d.mm"

theorem frege108d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume frege108d.r: |- ( ph -> R e. _V )
  assume frege108d.a: |- ( ph -> A e. _V )
  assume frege108d.b: |- ( ph -> B e. _V )
  assume frege108d.c: |- ( ph -> C e. _V )
  assume frege108d.ac: |- ( ph -> ( A ( t+ ` R ) C \/ A = C ) )
  assume frege108d.cb: |- ( ph -> C R B )


  assert |- ( ph -> ( A ( t+ ` R ) B \/ A = B ) )

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
    frege108d.r
    frege108d.a
    frege108d.b
    frege108d.c
    frege108d.ac
    frege108d.cb
    frege102d
    frege106d
end
