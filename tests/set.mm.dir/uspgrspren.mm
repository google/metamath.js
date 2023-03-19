include "wcel.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "cen.mm"
include "wbr.mm"
include "uspgrbispr.mm"
include "bren.mm"
include "sylibr.mm"

theorem uspgrspren
  let vv: setvar v
  let cP: class P
  let ve: setvar e
  let cG: class G
  let cV: class V
  let cW: class W
  let vq: setvar q
  let vg: setvar g
  let vf: setvar f
  let vk: setvar k
  let vx: setvar x
  assume uspgrsprf.p: |- P = ~P ( Pairs ` V )
  assume uspgrsprf.g: |- G = { <. v , e >. | ( v = V /\ E. q e. USPGraph ( ( Vtx ` q ) = v /\ ( Edg ` q ) = e ) ) }

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
  disjoint W q
  disjoint G g
  disjoint P g
  disjoint e g
  disjoint g v
  disjoint G f
  disjoint P f
  disjoint f g
  disjoint k x
  assert |- ( V e. W -> G ~~ P )

  proof
    cV
    cW
    wcel
    cG
    cP
    vf
    cv
    wf1o
    vf
    wex
    cG
    cP
    cen
    wbr
    vv
    cP
    ve
    vf
    cG
    cV
    cW
    vq
    uspgrsprf.p
    uspgrsprf.g
    uspgrbispr
    cG
    cP
    vf
    bren
    sylibr
end
