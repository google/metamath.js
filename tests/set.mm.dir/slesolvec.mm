include "c0.mm"
include "wne.mm"
include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cfn.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "simpr.mm"
include "simpl.mm"
include "3jca.mm"
include "ex.mm"
include "adantr.mm"
include "syl5com.mm"
include "impcom.mm"
include "anim12i.mm"
include "cbs.mm"
include "cfv.mm"
include "cxp.mm"
include "cmap.mm"
include "eqid.mm"
include "mavmulsolcl.mm"
include "syl2anc.mm"

theorem slesolvec
  let cA: class A
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume slesolex.a: |- A = ( N Mat R )
  assume slesolex.b: |- B = ( Base ` A )
  assume slesolex.v: |- V = ( ( Base ` R ) ^m N )
  assume slesolex.x: |- .x. = ( R maVecMul <. N , N >. )


  assert |- ( ( ( N =/= (/) /\ R e. Ring ) /\ ( X e. B /\ Y e. V ) ) -> ( ( X .x. Z ) = Y -> Z e. V ) )

  proof
    cN
    c0
    wne
    #
    cR
    crg
    wcel
    #
    wa
    #
    cX
    cB
    wcel
    #
    cY
    cV
    wcel
    #
    wa
    #
    wa
    cN
    cfn
    wcel
    #
    @6
    @0
    w3a
    #
    @1
    @4
    wa
    cX
    cZ
    c.x
    co
    cY
    wceq
    cZ
    cV
    wcel
    wi
    @5
    @2
    @7
    @3
    @2
    @7
    wi
    @4
    @3
    @6
    @2
    @7
    @3
    @6
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cX
    slesolex.a
    slesolex.b
    matrcl
    simpld
    @0
    @6
    @7
    wi
    @1
    @0
    @6
    @7
    @0
    @6
    wa
    @6
    @6
    @0
    @0
    @6
    simpr
    #
    @8
    @0
    @6
    simpl
    3jca
    ex
    adantr
    syl5com
    adantr
    impcom
    @2
    @1
    @5
    @4
    @0
    @1
    simpr
    @3
    @4
    simpr
    anim12i
    cX
    cR
    cbs
    cfv
    #
    @9
    cN
    cN
    cxp
    cmap
    co
    #
    cV
    cR
    c.x
    cV
    cN
    cN
    crg
    cZ
    cY
    @9
    eqid
    @10
    eqid
    slesolex.v
    slesolex.x
    slesolex.v
    mavmulsolcl
    syl2anc
end
