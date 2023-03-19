include "wcel.mm"
include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "uspgrymrelen.mm"
include "bren.mm"
include "sylib.mm"

theorem uspgrbisymrel
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let cR: class R
  let ve: setvar e
  let vf: setvar f
  let cG: class G
  let cV: class V
  let cW: class W
  let vr: setvar r
  let vq: setvar q
  let vg: setvar g
  let vp: setvar p
  let vk: setvar k
  assume uspgrbisymrel.g: |- G = { <. v , e >. | ( v = V /\ E. q e. USPGraph ( ( Vtx ` q ) = v /\ ( Edg ` q ) = e ) ) }
  assume uspgrbisymrel.r: |- R = { r e. ~P ( V X. V ) | A. x e. V A. y e. V ( x r y <-> y r x ) }

  disjoint V e
  disjoint V q
  disjoint V v
  disjoint e q
  disjoint e v
  disjoint q v
  disjoint V r
  disjoint V x
  disjoint V y
  disjoint r x
  disjoint r y
  disjoint x y
  disjoint W e
  disjoint W q
  disjoint W v
  disjoint W x
  disjoint W y
  disjoint G f
  disjoint R f
  disjoint G g
  disjoint f g
  disjoint R p
  disjoint f p
  disjoint V g
  disjoint V p
  disjoint p r
  disjoint p x
  disjoint p y
  disjoint k x
  assert |- ( V e. W -> E. f f : G -1-1-onto-> R )

  proof
    cV
    cW
    wcel
    cG
    cR
    cen
    wbr
    cG
    cR
    vf
    cv
    wf1o
    vf
    wex
    vx
    vy
    vv
    cR
    ve
    cG
    cV
    cW
    vr
    vq
    uspgrbisymrel.g
    uspgrbisymrel.r
    uspgrymrelen
    cG
    cR
    vf
    bren
    sylib
end
