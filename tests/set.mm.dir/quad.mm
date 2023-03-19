include "csqrt.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c4.mm"
include "cmul.mm"
include "cmin.mm"
include "cc.mm"
include "sqcld.mm"
include "wcel.mm"
include "4cn.mm"
include "mulcld.mm"
include "mulcl.mm"
include "sylancr.mm"
include "subcld.mm"
include "eqeltrd.mm"
include "sqrtcld.mm"
include "sqsqrtd.mm"
include "eqtrd.mm"
include "quad2.mm"

theorem quad
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cX: class X
  assume quad.a: |- ( ph -> A e. CC )
  assume quad.z: |- ( ph -> A =/= 0 )
  assume quad.b: |- ( ph -> B e. CC )
  assume quad.c: |- ( ph -> C e. CC )
  assume quad.x: |- ( ph -> X e. CC )
  assume quad.d: |- ( ph -> D = ( ( B ^ 2 ) - ( 4 x. ( A x. C ) ) ) )


  assert |- ( ph -> ( ( ( A x. ( X ^ 2 ) ) + ( ( B x. X ) + C ) ) = 0 <-> ( X = ( ( -u B + ( sqrt ` D ) ) / ( 2 x. A ) ) \/ X = ( ( -u B - ( sqrt ` D ) ) / ( 2 x. A ) ) ) ) )

  proof
    wph
    cA
    cB
    cC
    cD
    csqrt
    cfv
    #
    cX
    quad.a
    quad.z
    quad.b
    quad.c
    quad.x
    wph
    cD
    wph
    cD
    cB
    c2
    cexp
    co
    #
    c4
    cA
    cC
    cmul
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cc
    quad.d
    wph
    @1
    @3
    wph
    cB
    quad.b
    sqcld
    wph
    c4
    cc
    wcel
    @2
    cc
    wcel
    @3
    cc
    wcel
    4cn
    wph
    cA
    cC
    quad.a
    quad.c
    mulcld
    c4
    @2
    mulcl
    sylancr
    subcld
    eqeltrd
    #
    sqrtcld
    wph
    @0
    c2
    cexp
    co
    cD
    @4
    wph
    cD
    @5
    sqsqrtd
    quad.d
    eqtrd
    quad2
end
