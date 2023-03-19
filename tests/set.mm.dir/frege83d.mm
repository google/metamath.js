include "cun.mm"
include "ssun1.mm"
include "sseldi.mm"
include "frege81d.mm"

theorem frege83d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cU: class U
  let cV: class V
  assume frege83d.r: |- ( ph -> R e. _V )
  assume frege83d.a: |- ( ph -> A e. U )
  assume frege83d.b: |- ( ph -> B e. _V )
  assume frege83d.ab: |- ( ph -> A ( t+ ` R ) B )
  assume frege83d.he: |- ( ph -> ( R " ( U u. V ) ) C_ ( U u. V ) )


  assert |- ( ph -> B e. ( U u. V ) )

  proof
    wph
    cA
    cB
    cR
    cU
    cV
    cun
    #
    frege83d.r
    wph
    cU
    @0
    cA
    cU
    cV
    ssun1
    frege83d.a
    sseldi
    frege83d.b
    frege83d.ab
    frege83d.he
    frege81d
end
