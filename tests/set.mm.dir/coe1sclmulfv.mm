include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cn0.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cco1.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "wceq.mm"
include "coe1sclmul.mm"
include "3expb.mm"
include "3adant3.mm"
include "fveq1d.mm"
include "simp3.mm"
include "cvv.mm"
include "nn0ex.mm"
include "a1i.mm"
include "simp2l.mm"
include "cbs.mm"
include "wf.mm"
include "wfn.mm"
include "simp2r.mm"
include "eqid.mm"
include "coe1f.mm"
include "ffn.mm"
include "3syl.mm"
include "eqidd.mm"
include "ofc1.mm"
include "mpdan.mm"
include "eqtrd.mm"

theorem coe1sclmulfv
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cK: class K
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vx: setvar x
  assume coe1sclmul.p: |- P = ( Poly1 ` R )
  assume coe1sclmul.b: |- B = ( Base ` P )
  assume coe1sclmul.k: |- K = ( Base ` R )
  assume coe1sclmul.a: |- A = ( algSc ` P )
  assume coe1sclmul.t: |- .xb = ( .r ` P )
  assume coe1sclmul.u: |- .x. = ( .r ` R )


  assert |- ( ( R e. Ring /\ ( X e. K /\ Y e. B ) /\ .0. e. NN0 ) -> ( ( coe1 ` ( ( A ` X ) .xb Y ) ) ` .0. ) = ( X .x. ( ( coe1 ` Y ) ` .0. ) ) )

  proof
    cR
    crg
    wcel
    #
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
    c.0
    cn0
    wcel
    #
    w3a
    #
    c.0
    cX
    cA
    cfv
    cY
    c.xb
    co
    cco1
    cfv
    #
    cfv
    c.0
    cn0
    cX
    csn
    cxp
    cY
    cco1
    cfv
    #
    c.x
    cof
    co
    #
    cfv
    #
    cX
    c.0
    @7
    cfv
    #
    c.x
    co
    #
    @5
    c.0
    @6
    @8
    @0
    @3
    @6
    @8
    wceq
    #
    @4
    @0
    @1
    @2
    @12
    cA
    cB
    cP
    cR
    c.xb
    c.x
    cK
    cX
    cY
    coe1sclmul.p
    coe1sclmul.b
    coe1sclmul.k
    coe1sclmul.a
    coe1sclmul.t
    coe1sclmul.u
    coe1sclmul
    3expb
    3adant3
    fveq1d
    @5
    @4
    @9
    @11
    wceq
    @0
    @3
    @4
    simp3
    @5
    cn0
    cX
    @10
    c.x
    @7
    cvv
    cK
    c.0
    cn0
    cvv
    wcel
    @5
    nn0ex
    a1i
    @0
    @1
    @2
    @4
    simp2l
    @5
    @2
    cn0
    cR
    cbs
    cfv
    #
    @7
    wf
    @7
    cn0
    wfn
    @0
    @1
    @2
    @4
    simp2r
    @7
    cB
    cP
    cR
    cY
    @13
    @7
    eqid
    coe1sclmul.b
    coe1sclmul.p
    @13
    eqid
    coe1f
    cn0
    @13
    @7
    ffn
    3syl
    @5
    @4
    wa
    @10
    eqidd
    ofc1
    mpdan
    eqtrd
end
