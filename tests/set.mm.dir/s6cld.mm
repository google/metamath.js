include "cs5.mm"
include "cs6.mm"
include "df-s6.mm"
include "s5cld.mm"
include "cats1cld.mm"

theorem s6cld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cX: class X
  assume s2cld.1: |- ( ph -> A e. X )
  assume s2cld.2: |- ( ph -> B e. X )
  assume s3cld.3: |- ( ph -> C e. X )
  assume s4cld.4: |- ( ph -> D e. X )
  assume s5cld.5: |- ( ph -> E e. X )
  assume s6cld.6: |- ( ph -> F e. X )


  assert |- ( ph -> <" A B C D E F "> e. Word X )

  proof
    wph
    cX
    cA
    cB
    cC
    cD
    cE
    cs5
    cA
    cB
    cC
    cD
    cE
    cF
    cs6
    cF
    cA
    cB
    cC
    cD
    cE
    cF
    df-s6
    wph
    cA
    cB
    cC
    cD
    cE
    cX
    s2cld.1
    s2cld.2
    s3cld.3
    s4cld.4
    s5cld.5
    s5cld
    s6cld.6
    cats1cld
end
