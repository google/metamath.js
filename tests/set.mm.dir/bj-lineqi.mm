include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cmin.mm"
include "cdiv.mm"
include "bj-lineq.mm"
include "mpbid.mm"

theorem bj-lineqi
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
  assume bj-lineqi.1: |- ( ph -> ( ( A x. X ) + B ) = Y )


  assert |- ( ph -> X = ( ( Y - B ) / A ) )

  proof
    wph
    cA
    cX
    cmul
    co
    cB
    caddc
    co
    cY
    wceq
    cX
    cY
    cB
    cmin
    co
    cA
    cdiv
    co
    wceq
    bj-lineqi.1
    wph
    cA
    cB
    cX
    cY
    bj-lineq.a
    bj-lineq.b
    bj-lineq.x
    bj-lineq.y
    bj-lineq.n0
    bj-lineq
    mpbid
end
