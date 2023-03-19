include "wcel.mm"
include "cs1.mm"
include "cword.mm"
include "s1cl.mm"
include "syl.mm"

theorem s1cld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume s1cld.1: |- ( ph -> A e. B )


  assert |- ( ph -> <" A "> e. Word B )

  proof
    wph
    cA
    cB
    wcel
    cA
    cs1
    cB
    cword
    wcel
    s1cld.1
    cA
    cB
    s1cl
    syl
end
