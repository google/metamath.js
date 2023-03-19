include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cfrlm.mm"
include "co.mm"
include "cplusg.mm"
include "cfv.mm"
include "cof.mm"
include "cfn.mm"
include "cvv.mm"
include "wceq.mm"
include "matrcl.mm"
include "adantr.mm"
include "eqid.mm"
include "matplusg.mm"
include "syl6eqr.mm"
include "syl.mm"
include "oveqd.mm"
include "cbs.mm"
include "simprd.mm"
include "simpld.mm"
include "xpfi.mm"
include "syl2anc.mm"
include "simpl.mm"
include "matbas.mm"
include "eleqtrrd.mm"
include "simpr.mm"
include "frlmplusgval.mm"
include "eqtr3d.mm"

theorem matplusg2
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
  let cN: class N
  let cX: class X
  let cY: class Y
  assume matplusg2.a: |- A = ( N Mat R )
  assume matplusg2.b: |- B = ( Base ` A )
  assume matplusg2.p: |- .+b = ( +g ` A )
  assume matplusg2.q: |- .+ = ( +g ` R )


  assert |- ( ( X e. B /\ Y e. B ) -> ( X .+b Y ) = ( X oF .+ Y ) )

  proof
    cX
    cB
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
    cplusg
    cfv
    #
    co
    cX
    cY
    c.pb
    co
    cX
    cY
    c.pl
    cof
    co
    @2
    @5
    c.pb
    cX
    cY
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
    c.pb
    wceq
    @0
    @8
    @1
    cA
    cB
    cR
    cN
    cX
    matplusg2.a
    matplusg2.b
    matrcl
    adantr
    #
    @8
    @5
    cA
    cplusg
    cfv
    c.pb
    cA
    cR
    @4
    cN
    cvv
    matplusg2.a
    @4
    eqid
    #
    matplusg
    matplusg2.p
    syl6eqr
    syl
    oveqd
    @2
    @4
    cbs
    cfv
    #
    c.pl
    @5
    cR
    cX
    cY
    @3
    cvv
    cfn
    @4
    @10
    @11
    eqid
    @2
    @6
    @7
    @9
    simprd
    @2
    @6
    @6
    @3
    cfn
    wcel
    @2
    @6
    @7
    @9
    simpld
    #
    @12
    cN
    cN
    xpfi
    syl2anc
    @2
    cX
    cB
    @11
    @0
    @1
    simpl
    @2
    @11
    cA
    cbs
    cfv
    #
    cB
    @2
    @8
    @11
    @13
    wceq
    @9
    cA
    cR
    @4
    cN
    cvv
    matplusg2.a
    @10
    matbas
    syl
    matplusg2.b
    syl6eqr
    #
    eleqtrrd
    @2
    cY
    cB
    @11
    @0
    @1
    simpr
    @14
    eleqtrrd
    matplusg2.q
    @5
    eqid
    frlmplusgval
    eqtr3d
end
