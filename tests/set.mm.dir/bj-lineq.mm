include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cmin.mm"
include "cdiv.mm"
include "mulcld.mm"
include "addlsub.mm"
include "subcld.mm"
include "bj-rdiv.mm"
include "bitrd.mm"

theorem bj-lineq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cX: class X
  let cY: class Y
  assume bj-lineq.a: |- ( ph -> A e. CC )
  assume bj-lineq.b: |- ( ph -> B e. CC )
  assume bj-lineq.x: |- ( ph -> X e. CC )
  assume bj-lineq.y: |- ( ph -> Y e. CC )
  assume bj-lineq.n0: |- ( ph -> A =/= 0 )


  assert |- ( ph -> ( ( ( A x. X ) + B ) = Y <-> X = ( ( Y - B ) / A ) ) )

  proof
    wph
    cA
    cX
    cmul
    co
    #
    cB
    caddc
    co
    cY
    wceq
    @0
    cY
    cB
    cmin
    co
    #
    wceq
    cX
    @1
    cA
    cdiv
    co
    wceq
    wph
    @0
    cB
    cY
    wph
    cA
    cX
    bj-lineq.a
    bj-lineq.x
    mulcld
    bj-lineq.b
    bj-lineq.y
    addlsub
    wph
    cA
    cX
    @1
    bj-lineq.a
    bj-lineq.x
    wph
    cY
    cB
    bj-lineq.y
    bj-lineq.b
    subcld
    bj-lineq.n0
    bj-rdiv
    bitrd
end
