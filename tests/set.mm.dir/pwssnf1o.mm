include "wcel.mm"
include "wa.mm"
include "wf1o.mm"
include "csn.mm"
include "cmap.mm"
include "co.mm"
include "cvv.mm"
include "cbs.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "simpr.mm"
include "mapsnf1o.mm"
include "sylancr.mm"
include "wceq.mm"
include "wb.mm"
include "snex.mm"
include "pwsbas.mm"
include "mpan2.mm"
include "adantr.mm"
include "syl6reqr.mm"
include "f1oeq3.mm"
include "syl.mm"
include "mpbird.mm"

theorem pwssnf1o
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cR: class R
  let cF: class F
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  assume pwssnf1o.y: |- Y = ( R ^s { I } )
  assume pwssnf1o.b: |- B = ( Base ` R )
  assume pwssnf1o.f: |- F = ( x e. B |-> ( { I } X. { x } ) )
  assume pwssnf1o.c: |- C = ( Base ` Y )

  disjoint Y x
  disjoint R x
  disjoint I x
  disjoint B x
  disjoint C x
  disjoint W x
  assert |- ( ( R e. V /\ I e. W ) -> F : B -1-1-onto-> C )

  proof
    cR
    cV
    wcel
    #
    cI
    cW
    wcel
    #
    wa
    #
    cB
    cC
    cF
    wf1o
    #
    cB
    cB
    cI
    csn
    #
    cmap
    co
    #
    cF
    wf1o
    #
    @2
    cB
    cvv
    wcel
    @1
    @6
    cB
    cR
    cbs
    cfv
    cvv
    pwssnf1o.b
    cR
    cbs
    fvex
    eqeltri
    @0
    @1
    simpr
    vx
    cB
    cF
    cI
    cvv
    cW
    pwssnf1o.f
    mapsnf1o
    sylancr
    @2
    cC
    @5
    wceq
    @3
    @6
    wb
    @2
    @5
    cY
    cbs
    cfv
    #
    cC
    @0
    @5
    @7
    wceq
    #
    @1
    @0
    @4
    cvv
    wcel
    @8
    cI
    snex
    cB
    cR
    @4
    cV
    cvv
    cY
    pwssnf1o.y
    pwssnf1o.b
    pwsbas
    mpan2
    adantr
    pwssnf1o.c
    syl6reqr
    cC
    @5
    cB
    cF
    f1oeq3
    syl
    mpbird
end
