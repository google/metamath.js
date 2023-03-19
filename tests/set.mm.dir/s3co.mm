include "cs2.mm"
include "cs3.mm"
include "cfv.mm"
include "df-s3.mm"
include "s2cld.mm"
include "s2co.mm"
include "cats1co.mm"

theorem s3co
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cX: class X
  let cY: class Y
  assume s2co.1: |- ( ph -> F : X --> Y )
  assume s2co.2: |- ( ph -> A e. X )
  assume s2co.3: |- ( ph -> B e. X )
  assume s3co.4: |- ( ph -> C e. X )


  assert |- ( ph -> ( F o. <" A B C "> ) = <" ( F ` A ) ( F ` B ) ( F ` C ) "> )

  proof
    wph
    cX
    cY
    cA
    cB
    cs2
    cA
    cB
    cC
    cs3
    cA
    cF
    cfv
    #
    cB
    cF
    cfv
    #
    cs2
    cF
    @0
    @1
    cC
    cF
    cfv
    #
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
    s2co.2
    s2co.3
    s2cld
    s3co.4
    s2co.1
    wph
    cA
    cB
    cF
    cX
    cY
    s2co.1
    s2co.2
    s2co.3
    s2co
    @0
    @1
    @2
    df-s3
    cats1co
end
