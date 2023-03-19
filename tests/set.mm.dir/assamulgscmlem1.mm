include "wcel.mm"
include "wa.mm"
include "casa.mm"
include "cur.mm"
include "cfv.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "clmod.mm"
include "assalmod.mm"
include "crg.mm"
include "assaring.mm"
include "eqid.mm"
include "ringidcl.mm"
include "syl.mm"
include "lmodvs1.mm"
include "eqcomd.mm"
include "syl2anc.mm"
include "adantl.mm"
include "simpll.mm"
include "simplr.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "mgpbas.mm"
include "ringidval.mm"
include "mulg0.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem assamulgscmlem1
  let cA: class A
  let cB: class B
  let c.x: class .x.
  let cE: class E
  let c.ex: class .^
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let cW: class W
  let cX: class X
  assume assamulgscm.v: |- V = ( Base ` W )
  assume assamulgscm.f: |- F = ( Scalar ` W )
  assume assamulgscm.b: |- B = ( Base ` F )
  assume assamulgscm.s: |- .x. = ( .s ` W )
  assume assamulgscm.g: |- G = ( mulGrp ` F )
  assume assamulgscm.p: |- .^ = ( .g ` G )
  assume assamulgscm.h: |- H = ( mulGrp ` W )
  assume assamulgscm.e: |- E = ( .g ` H )


  assert |- ( ( ( A e. B /\ X e. V ) /\ W e. AssAlg ) -> ( 0 E ( A .x. X ) ) = ( ( 0 .^ A ) .x. ( 0 E X ) ) )

  proof
    cA
    cB
    wcel
    #
    cX
    cV
    wcel
    #
    wa
    #
    cW
    casa
    wcel
    #
    wa
    #
    cW
    cur
    cfv
    #
    cF
    cur
    cfv
    #
    @5
    c.x
    co
    #
    cc0
    cA
    cX
    c.x
    co
    #
    cE
    co
    #
    cc0
    cA
    c.ex
    co
    #
    cc0
    cX
    cE
    co
    #
    c.x
    co
    @3
    @5
    @7
    wceq
    #
    @2
    @3
    cW
    clmod
    wcel
    #
    @5
    cV
    wcel
    #
    @12
    cW
    assalmod
    #
    @3
    cW
    crg
    wcel
    @14
    cW
    assaring
    cV
    cW
    @5
    assamulgscm.v
    @5
    eqid
    #
    ringidcl
    syl
    @13
    @14
    wa
    @7
    @5
    c.x
    @6
    cF
    cV
    cW
    @5
    assamulgscm.v
    assamulgscm.f
    assamulgscm.s
    @6
    eqid
    #
    lmodvs1
    eqcomd
    syl2anc
    adantl
    @4
    @8
    cV
    wcel
    #
    @9
    @5
    wceq
    @4
    @13
    @0
    @1
    @18
    @3
    @13
    @2
    @15
    adantl
    @0
    @1
    @3
    simpll
    #
    @0
    @1
    @3
    simplr
    #
    cA
    c.x
    cF
    cB
    cV
    cW
    cX
    assamulgscm.v
    assamulgscm.f
    assamulgscm.s
    assamulgscm.b
    lmodvscl
    syl3anc
    cV
    cE
    cH
    @8
    @5
    cV
    cW
    cH
    assamulgscm.h
    assamulgscm.v
    mgpbas
    #
    cW
    @5
    cH
    assamulgscm.h
    @16
    ringidval
    #
    assamulgscm.e
    mulg0
    syl
    @4
    @10
    @6
    @11
    @5
    c.x
    @4
    @0
    @10
    @6
    wceq
    @19
    cB
    c.ex
    cG
    cA
    @6
    cB
    cF
    cG
    assamulgscm.g
    assamulgscm.b
    mgpbas
    cF
    @6
    cG
    assamulgscm.g
    @17
    ringidval
    assamulgscm.p
    mulg0
    syl
    @4
    @1
    @11
    @5
    wceq
    @20
    cV
    cE
    cH
    cX
    @5
    @21
    @22
    assamulgscm.e
    mulg0
    syl
    oveq12d
    3eqtr4d
end
