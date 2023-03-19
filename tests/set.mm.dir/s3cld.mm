include "cs2.mm"
include "cs3.mm"
include "df-s3.mm"
include "s2cld.mm"
include "cats1cld.mm"

theorem s3cld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cX: class X
  assume s2cld.1: |- ( ph -> A e. X )
  assume s2cld.2: |- ( ph -> B e. X )
  assume s3cld.3: |- ( ph -> C e. X )


  assert |- ( ph -> <" A B C "> e. Word X )

  proof
    wph
    cX
    cA
    cB
    cs2
    cA
    cB
    cC
    cs3
    cC
    cA
    cB
    cC
    df-s3
    wph
    cA
    cB
    cX
    s2cld.1
    s2cld.2
    s2cld
    s3cld.3
    cats1cld
end
