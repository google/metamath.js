include "cs3.mm"
include "cs4.mm"
include "df-s4.mm"
include "s3cld.mm"
include "cats1cld.mm"

theorem s4cld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cX: class X
  assume s2cld.1: |- ( ph -> A e. X )
  assume s2cld.2: |- ( ph -> B e. X )
  assume s3cld.3: |- ( ph -> C e. X )
  assume s4cld.4: |- ( ph -> D e. X )


  assert |- ( ph -> <" A B C D "> e. Word X )

  proof
    wph
    cX
    cA
    cB
    cC
    cs3
    cA
    cB
    cC
    cD
    cs4
    cD
    cA
    cB
    cC
    cD
    df-s4
    wph
    cA
    cB
    cC
    cX
    s2cld.1
    s2cld.2
    s3cld.3
    s3cld
    s4cld.4
    cats1cld
end
