include "crg.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "clt.mm"
include "cco1.mm"
include "c0g.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "eqid.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simprl.mm"
include "nn0red.mm"
include "simprr.mm"
include "ltned.mm"
include "coe1tmfv2.mm"
include "expr.mm"
include "ralrimiva.mm"
include "cbs.mm"
include "cxr.mm"
include "wb.mm"
include "ply1tmcl.mm"
include "nn0re.mm"
include "rexrd.mm"
include "3ad2ant3.mm"
include "deg1leb.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem deg1tmle
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let c.ex: class .^
  let cF: class F
  let cK: class K
  let cN: class N
  let cX: class X
  let vx: setvar x
  assume deg1tm.d: |- D = ( deg1 ` R )
  assume deg1tm.k: |- K = ( Base ` R )
  assume deg1tm.p: |- P = ( Poly1 ` R )
  assume deg1tm.x: |- X = ( var1 ` R )
  assume deg1tm.m: |- .x. = ( .s ` P )
  assume deg1tm.n: |- N = ( mulGrp ` P )
  assume deg1tm.e: |- .^ = ( .g ` N )


  assert |- ( ( R e. Ring /\ C e. K /\ F e. NN0 ) -> ( D ` ( C .x. ( F .^ X ) ) ) <_ F )

  proof
    cR
    crg
    wcel
    #
    cC
    cK
    wcel
    #
    cF
    cn0
    wcel
    #
    w3a
    #
    cC
    cF
    cX
    c.ex
    co
    c.x
    co
    #
    cD
    cfv
    cF
    cle
    wbr
    #
    cF
    vx
    cv
    #
    clt
    wbr
    #
    @6
    @4
    cco1
    cfv
    #
    cfv
    cR
    c0g
    cfv
    #
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    @3
    @11
    vx
    cn0
    @3
    @6
    cn0
    wcel
    #
    @7
    @10
    @3
    @13
    @7
    wa
    #
    wa
    #
    cC
    cF
    cP
    cR
    c.x
    c.ex
    @6
    cK
    cN
    cX
    @9
    @9
    eqid
    #
    deg1tm.k
    deg1tm.p
    deg1tm.x
    deg1tm.m
    deg1tm.n
    deg1tm.e
    @0
    @1
    @2
    @14
    simpl1
    @0
    @1
    @2
    @14
    simpl2
    @0
    @1
    @2
    @14
    simpl3
    #
    @3
    @13
    @7
    simprl
    @15
    cF
    @6
    @15
    cF
    @17
    nn0red
    @3
    @13
    @7
    simprr
    ltned
    coe1tmfv2
    expr
    ralrimiva
    @3
    @4
    cP
    cbs
    cfv
    #
    wcel
    cF
    cxr
    wcel
    #
    @5
    @12
    wb
    @18
    cC
    cF
    cP
    cR
    c.x
    c.ex
    cK
    cN
    cX
    deg1tm.k
    deg1tm.p
    deg1tm.x
    deg1tm.m
    deg1tm.n
    deg1tm.e
    @18
    eqid
    #
    ply1tmcl
    @2
    @0
    @19
    @1
    @2
    cF
    cF
    nn0re
    rexrd
    3ad2ant3
    vx
    @8
    @18
    cD
    cP
    cR
    @4
    cF
    @9
    deg1tm.d
    deg1tm.p
    @20
    @16
    @8
    eqid
    deg1leb
    syl2anc
    mpbird
end
