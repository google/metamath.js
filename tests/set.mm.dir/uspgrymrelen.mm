include "wcel.mm"
include "cspr.mm"
include "cfv.mm"
include "cpw.mm"
include "cen.mm"
include "wbr.mm"
include "eqid.mm"
include "uspgrspren.mm"
include "sprsymrelen.mm"
include "entr.mm"
include "syl2anc.mm"

theorem uspgrymrelen
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let cR: class R
  let ve: setvar e
  let cG: class G
  let cV: class V
  let cW: class W
  let vr: setvar r
  let vq: setvar q
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
  disjoint k x
  assert |- ( V e. W -> G ~~ R )

  proof
    cV
    cW
    wcel
    cG
    cV
    cspr
    cfv
    cpw
    #
    cen
    wbr
    @0
    cR
    cen
    wbr
    cG
    cR
    cen
    wbr
    vv
    @0
    ve
    cG
    cV
    cW
    vq
    @0
    eqid
    #
    uspgrbisymrel.g
    uspgrspren
    vx
    vy
    @0
    cR
    cV
    cW
    vr
    @1
    uspgrbisymrel.r
    sprsymrelen
    cG
    @0
    cR
    entr
    syl2anc
end
