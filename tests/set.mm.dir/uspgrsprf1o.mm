include "wcel.mm"
include "wf1.mm"
include "wfo.mm"
include "wf1o.mm"
include "uspgrsprf1.mm"
include "a1i.mm"
include "uspgrsprfo.mm"
include "df-f1o.mm"
include "sylanbrc.mm"

theorem uspgrsprf1o
  let vv: setvar v
  let cP: class P
  let ve: setvar e
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let vq: setvar q
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vw: setvar w
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x
  assume uspgrsprf.p: |- P = ~P ( Pairs ` V )
  assume uspgrsprf.g: |- G = { <. v , e >. | ( v = V /\ E. q e. USPGraph ( ( Vtx ` q ) = v /\ ( Edg ` q ) = e ) ) }
  assume uspgrsprf.f: |- F = ( g e. G |-> ( 2nd ` g ) )

  disjoint P e
  disjoint P g
  disjoint P v
  disjoint e g
  disjoint e v
  disjoint g v
  disjoint G g
  disjoint V e
  disjoint V v
  disjoint V q
  disjoint W q
  disjoint P e
  disjoint P q
  disjoint P v
  disjoint e q
  disjoint e v
  disjoint q v
  disjoint V e
  disjoint V q
  disjoint V v
  disjoint W e
  disjoint W v
  disjoint G g
  disjoint X g
  disjoint F a
  disjoint F b
  disjoint a b
  disjoint G a
  disjoint G b
  disjoint a g
  disjoint b g
  disjoint P a
  disjoint P b
  disjoint V a
  disjoint V b
  disjoint V f
  disjoint V w
  disjoint a f
  disjoint a e
  disjoint a v
  disjoint a w
  disjoint b f
  disjoint b e
  disjoint b v
  disjoint b w
  disjoint e f
  disjoint f v
  disjoint f w
  disjoint e w
  disjoint v w
  disjoint f q
  disjoint q w
  disjoint V p
  disjoint a p
  disjoint f p
  disjoint W a
  disjoint W b
  disjoint W p
  disjoint a q
  disjoint k x
  assert |- ( V e. W -> F : G -1-1-onto-> P )

  proof
    cV
    cW
    wcel
    #
    cG
    cP
    cF
    wf1
    #
    cG
    cP
    cF
    wfo
    cG
    cP
    cF
    wf1o
    @1
    @0
    vv
    cP
    ve
    vg
    cF
    cG
    cV
    vq
    uspgrsprf.p
    uspgrsprf.g
    uspgrsprf.f
    uspgrsprf1
    a1i
    vv
    cP
    ve
    vg
    cF
    cG
    cV
    cW
    vq
    uspgrsprf.p
    uspgrsprf.g
    uspgrsprf.f
    uspgrsprfo
    cG
    cP
    cF
    df-f1o
    sylanbrc
end
