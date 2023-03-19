include "catm.mm"
include "cfv.mm"
include "coc.mm"
include "ctrl.mm"
include "cltrn.mm"
include "ctendo.mm"
include "cv.mm"
include "wceq.mm"
include "crio.mm"
include "cjn.mm"
include "cmee.mm"
include "eqid.mm"
include "dihglbcpreN.mm"

theorem dihglbcN
  let vx: setvar x
  let cB: class B
  let cS: class S
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vq: setvar q
  let c.an: class ./\
  let vf: setvar f
  let vg: setvar g
  let vs: setvar s
  let c.or: class .\/
  let cA: class A
  let cE: class E
  let cF: class F
  let cP: class P
  let cR: class R
  let cT: class T
  assume dihglbc.b: |- B = ( Base ` K )
  assume dihglbc.g: |- G = ( glb ` K )
  assume dihglbc.h: |- H = ( LHyp ` K )
  assume dihglbc.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihglbc.l: |- .<_ = ( le ` K )

  disjoint .<_ x
  disjoint B x
  disjoint G x
  disjoint H x
  disjoint K x
  disjoint S x
  disjoint W x
  disjoint q x
  disjoint ./\ q
  disjoint ./\ x
  disjoint f g
  disjoint f q
  disjoint f s
  disjoint f x
  disjoint .<_ f
  disjoint g q
  disjoint g s
  disjoint g x
  disjoint .<_ g
  disjoint q s
  disjoint .<_ q
  disjoint s x
  disjoint .<_ s
  disjoint .\/ x
  disjoint A g
  disjoint A q
  disjoint A x
  disjoint B f
  disjoint B q
  disjoint B s
  disjoint E x
  disjoint F x
  disjoint G f
  disjoint G q
  disjoint G s
  disjoint H f
  disjoint H g
  disjoint H q
  disjoint H s
  disjoint I f
  disjoint I q
  disjoint I s
  disjoint K f
  disjoint K g
  disjoint K q
  disjoint K s
  disjoint P g
  disjoint R x
  disjoint S f
  disjoint S q
  disjoint S s
  disjoint T g
  disjoint T x
  disjoint W f
  disjoint W g
  disjoint W q
  disjoint W s
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( S C_ B /\ S =/= (/) ) /\ -. ( G ` S ) .<_ W ) -> ( I ` ( G ` S ) ) = |^|_ x e. S ( I ` x ) )

  proof
    vx
    cK
    catm
    cfv
    #
    cB
    cW
    cK
    coc
    cfv
    cfv
    #
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cS
    cW
    cK
    cltrn
    cfv
    cfv
    #
    vg
    cW
    cK
    ctendo
    cfv
    cfv
    #
    @1
    vg
    cv
    cfv
    vq
    cv
    wceq
    vg
    @3
    crio
    #
    cG
    cH
    cI
    cK
    cjn
    cfv
    #
    cK
    c.le
    cK
    cmee
    cfv
    #
    cW
    vq
    dihglbc.b
    dihglbc.g
    dihglbc.h
    dihglbc.i
    dihglbc.l
    @6
    eqid
    @7
    eqid
    @0
    eqid
    @1
    eqid
    @3
    eqid
    @2
    eqid
    @4
    eqid
    @5
    eqid
    dihglbcpreN
end
