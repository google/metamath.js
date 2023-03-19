include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cfrlm.mm"
include "co.mm"
include "cvsca.mm"
include "cfv.mm"
include "csn.mm"
include "cof.mm"
include "cfn.mm"
include "cvv.mm"
include "wceq.mm"
include "matrcl.mm"
include "adantl.mm"
include "eqid.mm"
include "matvsca.mm"
include "syl.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "cbs.mm"
include "simpld.mm"
include "xpfi.mm"
include "syl2anc.mm"
include "simpl.mm"
include "simpr.mm"
include "matbas.mm"
include "eleqtrrd.mm"
include "frlmvscafval.mm"
include "xpeq1i.mm"
include "oveq1i.mm"
include "eqtr3d.mm"

theorem matvsca2
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let cK: class K
  let cN: class N
  let cX: class X
  let cY: class Y
  assume matvsca2.a: |- A = ( N Mat R )
  assume matvsca2.b: |- B = ( Base ` A )
  assume matvsca2.k: |- K = ( Base ` R )
  assume matvsca2.v: |- .x. = ( .s ` A )
  assume matvsca2.t: |- .X. = ( .r ` R )
  assume matvsca2.c: |- C = ( N X. N )


  assert |- ( ( X e. K /\ Y e. B ) -> ( X .x. Y ) = ( ( C X. { X } ) oF .X. Y ) )

  proof
    cX
    cK
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cX
    cY
    cR
    cN
    cN
    cxp
    #
    cfrlm
    co
    #
    cvsca
    cfv
    #
    co
    #
    cX
    cY
    c.x
    co
    cC
    cX
    csn
    #
    cxp
    #
    cY
    c.xp
    cof
    #
    co
    #
    @2
    @5
    c.x
    cX
    cY
    @2
    @5
    cA
    cvsca
    cfv
    #
    c.x
    @2
    cN
    cfn
    wcel
    #
    cR
    cvv
    wcel
    #
    wa
    #
    @5
    @11
    wceq
    @1
    @14
    @0
    cA
    cB
    cR
    cN
    cY
    matvsca2.a
    matvsca2.b
    matrcl
    adantl
    #
    cA
    cR
    @4
    cN
    cvv
    matvsca2.a
    @4
    eqid
    #
    matvsca
    syl
    matvsca2.v
    syl6eqr
    oveqd
    @2
    @6
    @3
    @7
    cxp
    #
    cY
    @9
    co
    @10
    @2
    cX
    @4
    cbs
    cfv
    #
    cR
    @5
    c.xp
    @3
    cK
    cfn
    cY
    @4
    @16
    @18
    eqid
    matvsca2.k
    @2
    @12
    @12
    @3
    cfn
    wcel
    @2
    @12
    @13
    @15
    simpld
    #
    @19
    cN
    cN
    xpfi
    syl2anc
    @0
    @1
    simpl
    @2
    cY
    cB
    @18
    @0
    @1
    simpr
    @2
    @18
    cA
    cbs
    cfv
    #
    cB
    @2
    @14
    @18
    @20
    wceq
    @15
    cA
    cR
    @4
    cN
    cvv
    matvsca2.a
    @16
    matbas
    syl
    matvsca2.b
    syl6eqr
    eleqtrrd
    @5
    eqid
    matvsca2.t
    frlmvscafval
    @8
    @17
    cY
    @9
    cC
    @3
    @7
    matvsca2.c
    xpeq1i
    oveq1i
    syl6eqr
    eqtr3d
end
