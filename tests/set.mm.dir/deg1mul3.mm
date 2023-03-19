include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cco1.mm"
include "c0g.mm"
include "csupp.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cn0.mm"
include "csn.mm"
include "cxp.mm"
include "cmulr.mm"
include "cof.mm"
include "cbs.mm"
include "wceq.mm"
include "eqid.mm"
include "rrgss.mm"
include "sseli.mm"
include "coe1sclmul.mm"
include "syl3an2.mm"
include "oveq1d.mm"
include "cvv.mm"
include "nn0ex.mm"
include "a1i.mm"
include "simp1.mm"
include "simp2.mm"
include "wf.mm"
include "coe1f.mm"
include "3ad2ant3.mm"
include "rrgsupp.mm"
include "eqtrd.mm"
include "supeq1d.mm"
include "ply1ring.mm"
include "3ad2ant1.mm"
include "ply1sclf.mm"
include "3ad2ant2.mm"
include "ffvelrnd.mm"
include "simp3.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "deg1val.mm"
include "syl.mm"
include "3eqtr4d.mm"

theorem deg1mul3
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let cE: class E
  let cF: class F
  let cG: class G
  assume deg1mul3.d: |- D = ( deg1 ` R )
  assume deg1mul3.p: |- P = ( Poly1 ` R )
  assume deg1mul3.e: |- E = ( RLReg ` R )
  assume deg1mul3.b: |- B = ( Base ` P )
  assume deg1mul3.t: |- .x. = ( .r ` P )
  assume deg1mul3.a: |- A = ( algSc ` P )


  assert |- ( ( R e. Ring /\ F e. E /\ G e. B ) -> ( D ` ( ( A ` F ) .x. G ) ) = ( D ` G ) )

  proof
    cR
    crg
    wcel
    #
    cF
    cE
    wcel
    #
    cG
    cB
    wcel
    #
    w3a
    #
    cF
    cA
    cfv
    #
    cG
    c.x
    co
    #
    cco1
    cfv
    #
    cR
    c0g
    cfv
    #
    csupp
    co
    #
    cxr
    clt
    csup
    #
    cG
    cco1
    cfv
    #
    @7
    csupp
    co
    #
    cxr
    clt
    csup
    #
    @5
    cD
    cfv
    #
    cG
    cD
    cfv
    #
    @3
    cxr
    @8
    @11
    clt
    @3
    @8
    cn0
    cF
    csn
    cxp
    @10
    cR
    cmulr
    cfv
    #
    cof
    co
    #
    @7
    csupp
    co
    @11
    @3
    @6
    @16
    @7
    csupp
    @1
    @0
    cF
    cR
    cbs
    cfv
    #
    wcel
    #
    @2
    @6
    @16
    wceq
    cE
    @17
    cF
    @17
    cR
    cE
    deg1mul3.e
    @17
    eqid
    #
    rrgss
    sseli
    #
    cA
    cB
    cP
    cR
    c.x
    @15
    @17
    cF
    cG
    deg1mul3.p
    deg1mul3.b
    @19
    deg1mul3.a
    deg1mul3.t
    @15
    eqid
    #
    coe1sclmul
    syl3an2
    oveq1d
    @3
    @17
    cR
    @15
    cE
    cn0
    cvv
    cF
    @10
    @7
    deg1mul3.e
    @19
    @21
    @7
    eqid
    #
    cn0
    cvv
    wcel
    @3
    nn0ex
    a1i
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @2
    @0
    cn0
    @17
    @10
    wf
    @1
    @10
    cB
    cP
    cR
    cG
    @17
    @10
    eqid
    #
    deg1mul3.b
    deg1mul3.p
    @19
    coe1f
    3ad2ant3
    rrgsupp
    eqtrd
    supeq1d
    @3
    @5
    cB
    wcel
    #
    @13
    @9
    wceq
    @3
    cP
    crg
    wcel
    #
    @4
    cB
    wcel
    @2
    @24
    @0
    @1
    @25
    @2
    cP
    cR
    deg1mul3.p
    ply1ring
    3ad2ant1
    @3
    @17
    cB
    cF
    cA
    @0
    @1
    @17
    cB
    cA
    wf
    @2
    cA
    cB
    cP
    cR
    @17
    deg1mul3.p
    deg1mul3.a
    @19
    deg1mul3.b
    ply1sclf
    3ad2ant1
    @1
    @0
    @18
    @2
    @20
    3ad2ant2
    ffvelrnd
    @0
    @1
    @2
    simp3
    cB
    cP
    c.x
    @4
    cG
    deg1mul3.b
    deg1mul3.t
    ringcl
    syl3anc
    @6
    cB
    cD
    cP
    cR
    @5
    @7
    deg1mul3.d
    deg1mul3.p
    deg1mul3.b
    @22
    @6
    eqid
    deg1val
    syl
    @2
    @0
    @14
    @12
    wceq
    @1
    @10
    cB
    cD
    cP
    cR
    cG
    @7
    deg1mul3.d
    deg1mul3.p
    deg1mul3.b
    @22
    @23
    deg1val
    3ad2ant3
    3eqtr4d
end
