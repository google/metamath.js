include "wcel.mm"
include "whe.mm"
include "ctcl.mm"
include "cfv.mm"
include "wbr.mm"
include "wi.mm"
include "frege81.mm"
include "frege18.mm"
include "ax-mp.mm"

theorem frege82
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume frege82.x: |- X e. U
  assume frege82.y: |- Y e. V
  assume frege82.r: |- R e. W
  assume frege82.a: |- A e. B


  assert |- ( ( ph -> X e. A ) -> ( R hereditary A -> ( ph -> ( X ( t+ ` R ) Y -> Y e. A ) ) ) )

  proof
    cX
    cA
    wcel
    #
    cA
    cR
    whe
    #
    cX
    cY
    cR
    ctcl
    cfv
    wbr
    cY
    cA
    wcel
    wi
    #
    wi
    wi
    wph
    @0
    wi
    @1
    wph
    @2
    wi
    wi
    wi
    cA
    cB
    cR
    cU
    cV
    cW
    cX
    cY
    frege82.x
    frege82.y
    frege82.r
    frege82.a
    frege81
    @0
    @1
    @2
    wph
    frege18
    ax-mp
end
