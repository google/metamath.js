include "ct1.mm"
include "wcel.mm"
include "ccn.mm"
include "co.mm"
include "wa.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "ccl.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "wfn.mm"
include "wf.mm"
include "simplr.mm"
include "cnf.mm"
include "ffn.mm"
include "3syl.mm"
include "simpr3.mm"
include "ccld.mm"
include "simpll.mm"
include "simpr1.mm"
include "t1sncld.mm"
include "syl2anc.mm"
include "cnclima.mm"
include "simpr2.mm"
include "clsss2.mm"
include "eqsstr3d.mm"
include "fconst3.mm"
include "sylanbrc.mm"

theorem dnsconst
  let cA: class A
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  assume dnsconst.1: |- X = U. J
  assume dnsconst.2: |- Y = U. K


  assert |- ( ( ( K e. Fre /\ F e. ( J Cn K ) ) /\ ( P e. Y /\ A C_ ( `' F " { P } ) /\ ( ( cls ` J ) ` A ) = X ) ) -> F : X --> { P } )

  proof
    cK
    ct1
    wcel
    #
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    wa
    #
    cP
    cY
    wcel
    #
    cA
    cF
    ccnv
    cP
    csn
    #
    cima
    #
    wss
    #
    cA
    cJ
    ccl
    cfv
    cfv
    #
    cX
    wceq
    #
    w3a
    #
    wa
    #
    cF
    cX
    wfn
    #
    cX
    @5
    wss
    cX
    @4
    cF
    wf
    @10
    @1
    cX
    cY
    cF
    wf
    @11
    @0
    @1
    @9
    simplr
    #
    cF
    cJ
    cK
    cX
    cY
    dnsconst.1
    dnsconst.2
    cnf
    cX
    cY
    cF
    ffn
    3syl
    @10
    cX
    @7
    @5
    @2
    @3
    @6
    @8
    simpr3
    @10
    @5
    cJ
    ccld
    cfv
    wcel
    #
    @6
    @7
    @5
    wss
    @10
    @1
    @4
    cK
    ccld
    cfv
    wcel
    #
    @13
    @12
    @10
    @0
    @3
    @14
    @0
    @1
    @9
    simpll
    @2
    @3
    @6
    @8
    simpr1
    cP
    cK
    cY
    dnsconst.2
    t1sncld
    syl2anc
    @4
    cF
    cJ
    cK
    cnclima
    syl2anc
    @2
    @3
    @6
    @8
    simpr2
    @5
    cA
    cJ
    cX
    dnsconst.1
    clsss2
    syl2anc
    eqsstr3d
    cX
    cP
    cF
    fconst3
    sylanbrc
end
