include "abs3difd.mm"

theorem absnpncand
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume absnpncand.a: |- ( ph -> A e. CC )
  assume absnpncand.b: |- ( ph -> B e. CC )
  assume absnpncand.c: |- ( ph -> C e. CC )


  assert |- ( ph -> ( abs ` ( A - C ) ) <_ ( ( abs ` ( A - B ) ) + ( abs ` ( B - C ) ) ) )

  proof
    wph
    cA
    cC
    cB
    absnpncand.a
    absnpncand.c
    absnpncand.b
    abs3difd
end
