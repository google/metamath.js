include "cs6.mm"
include "cs7.mm"
include "df-s7.mm"
include "s6cld.mm"
include "cats1cld.mm"

theorem s7cld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cX: class X
  assume s2cld.1: |- ( ph -> A e. X )
  assume s2cld.2: |- ( ph -> B e. X )
  assume s3cld.3: |- ( ph -> C e. X )
  assume s4cld.4: |- ( ph -> D e. X )
  assume s5cld.5: |- ( ph -> E e. X )
  assume s6cld.6: |- ( ph -> F e. X )
  assume s7cld.7: |- ( ph -> G e. X )


  assert |- ( ph -> <" A B C D E F G "> e. Word X )

  proof
    wph
    cX
    cA
    cB
    cC
    cD
    cE
    cF
    cs6
    cA
    cB
    cC
    cD
    cE
    cF
    cG
    cs7
    cG
    cA
    cB
    cC
    cD
    cE
    cF
    cG
    df-s7
    wph
    cA
    cB
    cC
    cD
    cE
    cF
    cX
    s2cld.1
    s2cld.2
    s3cld.3
    s4cld.4
    s5cld.5
    s6cld.6
    s6cld
    s7cld.7
    cats1cld
end
