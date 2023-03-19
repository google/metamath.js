include "frege96d.mm"
include "frege77d.mm"

theorem frege87d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cU: class U
  assume frege87d.r: |- ( ph -> R e. _V )
  assume frege87d.a: |- ( ph -> A e. _V )
  assume frege87d.b: |- ( ph -> B e. _V )
  assume frege87d.c: |- ( ph -> C e. _V )
  assume frege87d.ac: |- ( ph -> A ( t+ ` R ) C )
  assume frege87d.cb: |- ( ph -> C R B )
  assume frege87d.ss: |- ( ph -> ( R " { A } ) C_ U )
  assume frege87d.he: |- ( ph -> ( R " U ) C_ U )


  assert |- ( ph -> B e. U )

  proof
    wph
    cA
    cB
    cR
    cU
    frege87d.r
    frege87d.a
    frege87d.b
    wph
    cA
    cB
    cC
    cR
    frege87d.r
    frege87d.a
    frege87d.b
    frege87d.c
    frege87d.ac
    frege87d.cb
    frege96d
    frege87d.he
    frege87d.ss
    frege77d
end
