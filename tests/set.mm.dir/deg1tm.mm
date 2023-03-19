include "crg.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "cn0.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "deg1tmle.mm"
include "3adant2r.mm"
include "cbs.mm"
include "cco1.mm"
include "eqid.mm"
include "ply1tmcl.mm"
include "simp3.mm"
include "coe1tmfv1.mm"
include "simp2r.mm"
include "eqnetrd.mm"
include "deg1ge.mm"
include "syl3anc.mm"
include "cxr.mm"
include "wb.mm"
include "deg1xrcl.mm"
include "syl.mm"
include "nn0red.mm"
include "rexrd.mm"
include "xrletri3.mm"
include "syl2anc.mm"
include "mpbir2and.mm"

theorem deg1tm
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
  let c.0: class .0.
  let vx: setvar x
  assume deg1tm.d: |- D = ( deg1 ` R )
  assume deg1tm.k: |- K = ( Base ` R )
  assume deg1tm.p: |- P = ( Poly1 ` R )
  assume deg1tm.x: |- X = ( var1 ` R )
  assume deg1tm.m: |- .x. = ( .s ` P )
  assume deg1tm.n: |- N = ( mulGrp ` P )
  assume deg1tm.e: |- .^ = ( .g ` N )
  assume deg1tm.z: |- .0. = ( 0g ` R )


  assert |- ( ( R e. Ring /\ ( C e. K /\ C =/= .0. ) /\ F e. NN0 ) -> ( D ` ( C .x. ( F .^ X ) ) ) = F )

  proof
    cR
    crg
    wcel
    #
    cC
    cK
    wcel
    #
    cC
    c.0
    wne
    #
    wa
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
    #
    cF
    wceq
    #
    @7
    cF
    cle
    wbr
    #
    cF
    @7
    cle
    wbr
    #
    @0
    @1
    @4
    @9
    @2
    cC
    cD
    cP
    cR
    c.x
    c.ex
    cF
    cK
    cN
    cX
    deg1tm.d
    deg1tm.k
    deg1tm.p
    deg1tm.x
    deg1tm.m
    deg1tm.n
    deg1tm.e
    deg1tmle
    3adant2r
    @5
    @6
    cP
    cbs
    cfv
    #
    wcel
    #
    @4
    cF
    @6
    cco1
    cfv
    #
    cfv
    #
    c.0
    wne
    @10
    @0
    @1
    @4
    @12
    @2
    @11
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
    @11
    eqid
    #
    ply1tmcl
    3adant2r
    #
    @0
    @3
    @4
    simp3
    #
    @5
    @14
    cC
    c.0
    @0
    @1
    @4
    @14
    cC
    wceq
    @2
    cC
    cF
    cP
    cR
    c.x
    c.ex
    cK
    cN
    cX
    c.0
    deg1tm.z
    deg1tm.k
    deg1tm.p
    deg1tm.x
    deg1tm.m
    deg1tm.n
    deg1tm.e
    coe1tmfv1
    3adant2r
    @0
    @1
    @2
    @4
    simp2r
    eqnetrd
    @13
    @11
    cD
    cP
    cR
    @6
    cF
    c.0
    deg1tm.d
    deg1tm.p
    @15
    deg1tm.z
    @13
    eqid
    deg1ge
    syl3anc
    @5
    @7
    cxr
    wcel
    #
    cF
    cxr
    wcel
    @8
    @9
    @10
    wa
    wb
    @5
    @12
    @18
    @16
    @11
    cD
    cP
    cR
    @6
    deg1tm.d
    deg1tm.p
    @15
    deg1xrcl
    syl
    @5
    cF
    @5
    cF
    @17
    nn0red
    rexrd
    @7
    cF
    xrletri3
    syl2anc
    mpbir2and
end
