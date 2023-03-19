include "wcel.mm"
include "cvv.mm"
include "cdsmm.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "elex.mm"
include "cprds.mm"
include "cress.mm"
include "dsmmval.mm"
include "fveq2d.mm"
include "wss.mm"
include "cv.mm"
include "c0g.mm"
include "wne.mm"
include "cdm.mm"
include "crab.mm"
include "cfn.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "eqid.mm"
include "ressbas2.mm"
include "ax-mp.mm"
include "syl6reqr.mm"
include "syl.mm"

theorem dsmmbase
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cV: class V
  let vs: setvar s
  let vr: setvar r
  assume dsmmval.b: |- B = { f e. ( Base ` ( S Xs_ R ) ) | { x e. dom R | ( f ` x ) =/= ( 0g ` ( R ` x ) ) } e. Fin }

  disjoint S f
  disjoint S x
  disjoint f x
  disjoint R f
  disjoint R x
  disjoint S s
  disjoint S r
  disjoint r s
  disjoint f s
  disjoint s x
  disjoint f r
  disjoint r x
  disjoint R s
  disjoint R r
  disjoint B s
  disjoint B r
  assert |- ( R e. V -> B = ( Base ` ( S (+)m R ) ) )

  proof
    cR
    cV
    wcel
    cR
    cvv
    wcel
    #
    cB
    cS
    cR
    cdsmm
    co
    #
    cbs
    cfv
    #
    wceq
    cR
    cV
    elex
    @0
    @2
    cS
    cR
    cprds
    co
    #
    cB
    cress
    co
    #
    cbs
    cfv
    #
    cB
    @0
    @1
    @4
    cbs
    vx
    cB
    cR
    cS
    vf
    cvv
    dsmmval.b
    dsmmval
    fveq2d
    cB
    @3
    cbs
    cfv
    #
    wss
    cB
    @5
    wceq
    cB
    vx
    cv
    #
    vf
    cv
    cfv
    @7
    cR
    cfv
    c0g
    cfv
    wne
    vx
    cR
    cdm
    crab
    cfn
    wcel
    #
    vf
    @6
    crab
    @6
    dsmmval.b
    @8
    vf
    @6
    ssrab2
    eqsstri
    cB
    @6
    @4
    @3
    @4
    eqid
    @6
    eqid
    ressbas2
    ax-mp
    syl6reqr
    syl
end
