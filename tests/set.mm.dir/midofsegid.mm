include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "ccgr.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp3r.mm"
include "simp3l.mm"
include "simprr.mm"
include "simprl3.mm"
include "cgrcomand.mm"
include "endofsegidand.mm"
include "eqcomd.mm"
include "expr.mm"
include "wo.mm"
include "3simpa.mm"
include "adantl.mm"
include "wi.mm"
include "simp2r.mm"
include "btwnconn3.mm"
include "syl122anc.mm"
include "adantr.mm"
include "mpd.mm"
include "mpjaod.mm"
include "ex.mm"

theorem midofsegid
  let cA: class A
  let cB: class B
  let cD: class D
  let cE: class E
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( D e. ( EE ` N ) /\ E e. ( EE ` N ) ) ) -> ( ( D Btwn <. A , B >. /\ E Btwn <. A , B >. /\ <. A , D >. Cgr <. A , E >. ) -> D = E ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    wa
    #
    cD
    @1
    wcel
    #
    cE
    @1
    wcel
    #
    wa
    #
    w3a
    #
    cD
    cA
    cB
    cop
    #
    cbtwn
    wbr
    #
    cE
    @9
    cbtwn
    wbr
    #
    cA
    cD
    cop
    #
    cA
    cE
    cop
    #
    ccgr
    wbr
    #
    w3a
    #
    cD
    cE
    wceq
    #
    @8
    @15
    wa
    #
    cD
    @13
    cbtwn
    wbr
    #
    @16
    cE
    @12
    cbtwn
    wbr
    #
    @8
    @15
    @18
    @16
    @8
    @15
    @18
    wa
    #
    wa
    cE
    cD
    @8
    @20
    cA
    cE
    cD
    cN
    @0
    @4
    @7
    simp1
    #
    @0
    @2
    @3
    @7
    simp2l
    #
    @0
    @4
    @5
    @6
    simp3r
    #
    @0
    @4
    @5
    @6
    simp3l
    #
    @8
    @15
    @18
    simprr
    @8
    @20
    cA
    cD
    cA
    cE
    cN
    @21
    @22
    @24
    @22
    @23
    @10
    @11
    @14
    @18
    @8
    simprl3
    cgrcomand
    endofsegidand
    eqcomd
    expr
    @8
    @15
    @19
    @16
    @8
    @15
    @19
    wa
    cA
    cD
    cE
    cN
    @21
    @22
    @24
    @23
    @8
    @15
    @19
    simprr
    @10
    @11
    @14
    @19
    @8
    simprl3
    endofsegidand
    expr
    @17
    @10
    @11
    wa
    #
    @18
    @19
    wo
    #
    @15
    @25
    @8
    @10
    @11
    @14
    3simpa
    adantl
    @8
    @25
    @26
    wi
    #
    @15
    @8
    @0
    @2
    @5
    @6
    @3
    @27
    @21
    @22
    @24
    @23
    @0
    @2
    @3
    @7
    simp2r
    cA
    cD
    cE
    cB
    cN
    btwnconn3
    syl122anc
    adantr
    mpd
    mpjaod
    ex
end
