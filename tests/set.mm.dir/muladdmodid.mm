include "cz.mm"
include "wcel.mm"
include "crp.mm"
include "cc0.mm"
include "cico.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "cmo.mm"
include "wceq.mm"
include "wa.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "w3a.mm"
include "wb.mm"
include "cxr.mm"
include "0red.mm"
include "rpxr.mm"
include "elico2.mm"
include "syl2anc.mm"
include "adantl.mm"
include "cc.mm"
include "zcn.mm"
include "rpcn.mm"
include "mulcl.mm"
include "syl2an.mm"
include "adantr.mm"
include "recn.mm"
include "3ad2ant1.mm"
include "addcomd.mm"
include "oveq1d.mm"
include "simp1.mm"
include "simpr.mm"
include "simpll.mm"
include "modcyc.mm"
include "syl3anc.mm"
include "anim12ci.mm"
include "3simpc.mm"
include "modid.mm"
include "3eqtrd.mm"
include "ex.mm"
include "sylbid.mm"
include "3impia.mm"

theorem muladdmodid
  let cA: class A
  let cM: class M
  let cN: class N


  assert |- ( ( N e. ZZ /\ M e. RR+ /\ A e. ( 0 [,) M ) ) -> ( ( ( N x. M ) + A ) mod M ) = A )

  proof
    cN
    cz
    wcel
    #
    cM
    crp
    wcel
    #
    cA
    cc0
    cM
    cico
    co
    wcel
    #
    cN
    cM
    cmul
    co
    #
    cA
    caddc
    co
    #
    cM
    cmo
    co
    #
    cA
    wceq
    #
    @0
    @1
    wa
    #
    @2
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    cA
    cM
    clt
    wbr
    #
    w3a
    #
    @6
    @1
    @2
    @11
    wb
    #
    @0
    @1
    cc0
    cr
    wcel
    cM
    cxr
    wcel
    @12
    @1
    0red
    cM
    rpxr
    cc0
    cM
    cA
    elico2
    syl2anc
    adantl
    @7
    @11
    @6
    @7
    @11
    wa
    #
    @5
    cA
    @3
    caddc
    co
    #
    cM
    cmo
    co
    #
    cA
    cM
    cmo
    co
    #
    cA
    @13
    @4
    @14
    cM
    cmo
    @13
    @3
    cA
    @7
    @3
    cc
    wcel
    #
    @11
    @0
    cN
    cc
    wcel
    cM
    cc
    wcel
    @17
    @1
    cN
    zcn
    cM
    rpcn
    cN
    cM
    mulcl
    syl2an
    adantr
    @11
    cA
    cc
    wcel
    #
    @7
    @8
    @9
    @18
    @10
    cA
    recn
    3ad2ant1
    adantl
    addcomd
    oveq1d
    @13
    @8
    @1
    @0
    @15
    @16
    wceq
    @11
    @8
    @7
    @8
    @9
    @10
    simp1
    #
    adantl
    @7
    @1
    @11
    @0
    @1
    simpr
    #
    adantr
    @0
    @1
    @11
    simpll
    cA
    cM
    cN
    modcyc
    syl3anc
    @13
    @8
    @1
    wa
    @9
    @10
    wa
    #
    @16
    cA
    wceq
    @7
    @1
    @11
    @8
    @20
    @19
    anim12ci
    @11
    @21
    @7
    @8
    @9
    @10
    3simpc
    adantl
    cA
    cM
    modid
    syl2anc
    3eqtrd
    ex
    sylbid
    3impia
end
