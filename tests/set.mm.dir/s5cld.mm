include "cs4.mm"
include "cs5.mm"
include "df-s5.mm"
include "s4cld.mm"
include "cats1cld.mm"

theorem s5cld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cX: class X
  assume s2cld.1: |- ( ph -> A e. X )
  assume s2cld.2: |- ( ph -> B e. X )
  assume s3cld.3: |- ( ph -> C e. X )
  assume s4cld.4: |- ( ph -> D e. X )
  assume s5cld.5: |- ( ph -> E e. X )


  assert |- ( ph -> <" A B C D E "> e. Word X )

  proof
    wph
    cX
    cA
    cB
    cC
    cD
    cs4
    cA
    cB
    cC
    cD
    cE
    cs5
    cE
    cA
    cB
    cC
    cD
    cE
    df-s5
    wph
    cA
    cB
    cC
    cD
    cX
    s2cld.1
    s2cld.2
    s3cld.3
    s4cld.4
    s4cld
    s5cld.5
    cats1cld
end
