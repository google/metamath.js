include "wcel.mm"
include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "fveq2.mm"
include "adantl.mm"
include "id.mm"
include "fvexd.mm"
include "fvmptd.mm"

theorem uspgrsprfv
  let vv: setvar v
  let cP: class P
  let ve: setvar e
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cV: class V
  let cX: class X
  let vq: setvar q
  let cW: class W
  let vk: setvar k
  let vx: setvar x
  assume uspgrsprf.p: |- P = ~P ( Pairs ` V )
  assume uspgrsprf.g: |- G = { <. v , e >. | ( v = V /\ E. q e. USPGraph ( ( Vtx ` q ) = v /\ ( Edg ` q ) = e ) ) }
  assume uspgrsprf.f: |- F = ( g e. G |-> ( 2nd ` g ) )

  disjoint X g
  disjoint P e
  disjoint P q
  disjoint P v
  disjoint e q
  disjoint e v
  disjoint q v
  disjoint V e
  disjoint V q
  disjoint V v
  disjoint G g
  disjoint W e
  disjoint W v
  disjoint k x
  assert |- ( X e. G -> ( F ` X ) = ( 2nd ` X ) )

  proof
    cX
    cG
    wcel
    #
    vg
    cX
    vg
    cv
    #
    c2nd
    cfv
    #
    cX
    c2nd
    cfv
    #
    cG
    cF
    cvv
    cF
    vg
    cG
    @2
    cmpt
    wceq
    @0
    uspgrsprf.f
    a1i
    @1
    cX
    wceq
    @2
    @3
    wceq
    @0
    @1
    cX
    c2nd
    fveq2
    adantl
    @0
    id
    @0
    cX
    c2nd
    fvexd
    fvmptd
end
