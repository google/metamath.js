include "wcel.mm"
include "cspr.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "wrex.mm"
include "copab.mm"
include "cmpt.mm"
include "c2nd.mm"
include "ccom.mm"
include "cvv.mm"
include "wf1o.mm"
include "wex.mm"
include "fvex.mm"
include "pwex.mm"
include "mptexg.mm"
include "mp1i.mm"
include "eqid.mm"
include "uspgrex.mm"
include "syl.mm"
include "coexg.mm"
include "syl2anc.mm"
include "sprsymrelf1o.mm"
include "uspgrsprf1o.mm"
include "f1oco.mm"
include "f1oeq1.mm"
include "spcegv.mm"
include "sylc.mm"

theorem uspgrbisymrelALT
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
  let vc: setvar c
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
  disjoint V f
  disjoint f r
  disjoint f x
  disjoint f y
  disjoint G g
  disjoint f g
  disjoint R p
  disjoint f p
  disjoint V g
  disjoint V p
  disjoint p r
  disjoint p x
  disjoint p y
  disjoint V c
  disjoint c f
  disjoint c p
  disjoint c r
  disjoint c x
  disjoint c y
  disjoint W c
  disjoint e g
  disjoint g v
  disjoint k x
  assert |- ( V e. W -> E. f f : G -1-1-onto-> R )

  proof
    cV
    cW
    wcel
    #
    vp
    cV
    cspr
    cfv
    #
    cpw
    #
    vc
    cv
    vx
    cv
    vy
    cv
    cpr
    wceq
    vc
    vp
    cv
    wrex
    vx
    vy
    copab
    #
    cmpt
    #
    vg
    cG
    vg
    cv
    c2nd
    cfv
    #
    cmpt
    #
    ccom
    #
    cvv
    wcel
    #
    cG
    cR
    @7
    wf1o
    #
    cG
    cR
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @0
    @4
    cvv
    wcel
    #
    @6
    cvv
    wcel
    #
    @8
    @2
    cvv
    wcel
    @12
    @0
    @1
    cV
    cspr
    fvex
    pwex
    vp
    @2
    @3
    cvv
    mptexg
    mp1i
    @0
    cG
    cvv
    wcel
    @13
    vv
    @2
    ve
    cG
    cV
    cW
    vq
    @2
    eqid
    #
    uspgrbisymrel.g
    uspgrex
    vg
    cG
    @5
    cvv
    mptexg
    syl
    @4
    @6
    cvv
    cvv
    coexg
    syl2anc
    @0
    @2
    cR
    @4
    wf1o
    cG
    @2
    @6
    wf1o
    @9
    vx
    vy
    @2
    cR
    @4
    cV
    cW
    vr
    vp
    vc
    @14
    uspgrbisymrel.r
    @4
    eqid
    sprsymrelf1o
    vv
    @2
    ve
    vg
    @6
    cG
    cV
    cW
    vq
    @14
    uspgrbisymrel.g
    @6
    eqid
    uspgrsprf1o
    cG
    @2
    cR
    @4
    @6
    f1oco
    syl2anc
    @11
    @9
    vf
    @7
    cvv
    cG
    cR
    @10
    @7
    f1oeq1
    spcegv
    sylc
end
