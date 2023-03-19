include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "cin.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "wss.mm"
include "diasslssN.mm"
include "sseqin2.mm"
include "sylib.mm"
include "wi.mm"
include "doca3N.mm"
include "ex.mm"
include "adantr.mm"
include "dvadiaN.mm"
include "expr.mm"
include "impbid.mm"
include "rabbi2dva.mm"
include "eqtr3d.mm"

theorem diarnN
  let vx: setvar x
  let cS: class S
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  assume dvadia.h: |- H = ( LHyp ` K )
  assume dvadia.u: |- U = ( ( DVecA ` K ) ` W )
  assume dvadia.i: |- I = ( ( DIsoA ` K ) ` W )
  assume dvadia.n: |- ._|_ = ( ( ocA ` K ) ` W )
  assume dvadia.s: |- S = ( LSubSp ` U )

  disjoint H x
  disjoint I x
  disjoint K x
  disjoint S x
  disjoint W x
  assert |- ( ( K e. HL /\ W e. H ) -> ran I = { x e. S | ( ._|_ ` ( ._|_ ` x ) ) = x } )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cS
    cI
    crn
    #
    cin
    #
    @1
    vx
    cv
    #
    c.pe
    cfv
    c.pe
    cfv
    @3
    wceq
    #
    vx
    cS
    crab
    @0
    @1
    cS
    wss
    @2
    @1
    wceq
    cS
    cU
    cH
    cI
    cK
    cW
    dvadia.h
    dvadia.u
    dvadia.i
    dvadia.s
    diasslssN
    @1
    cS
    sseqin2
    sylib
    @0
    @4
    vx
    cS
    @1
    @0
    @3
    cS
    wcel
    #
    wa
    @3
    @1
    wcel
    #
    @4
    @0
    @6
    @4
    wi
    @5
    @0
    @6
    @4
    cH
    cI
    cK
    c.pe
    cW
    @3
    dvadia.h
    dvadia.i
    dvadia.n
    doca3N
    ex
    adantr
    @0
    @5
    @4
    @6
    cS
    cU
    cH
    cI
    cK
    c.pe
    cW
    @3
    dvadia.h
    dvadia.u
    dvadia.i
    dvadia.n
    dvadia.s
    dvadiaN
    expr
    impbid
    rabbi2dva
    eqtr3d
end
