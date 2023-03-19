include "cs1.mm"
include "cs2.mm"
include "df-s2.mm"
include "s1cld.mm"
include "cats1cld.mm"

theorem s2cld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cX: class X
  assume s2cld.1: |- ( ph -> A e. X )
  assume s2cld.2: |- ( ph -> B e. X )


  assert |- ( ph -> <" A B "> e. Word X )

  proof
    wph
    cX
    cA
    cs1
    cA
    cB
    cs2
    cB
    cA
    cB
    df-s2
    wph
    cA
    cX
    s2cld.1
    s1cld
    s2cld.2
    cats1cld
end
