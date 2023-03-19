include "wcel.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "cfn.mm"
include "wa.mm"
include "cun.mm"
include "chash.mm"
include "cfv.mm"
include "cxad.mm"
include "co.mm"
include "wi.mm"
include "caddc.mm"
include "hashun.mm"
include "3expa.mm"
include "cr.mm"
include "hashcl.mm"
include "nn0red.mm"
include "anim12i.mm"
include "adantr.mm"
include "rexadd.mm"
include "syl.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "expcom.mm"
include "3ad2ant3.mm"
include "wn.mm"
include "cpnf.mm"
include "cvv.mm"
include "unexg.mm"
include "unfir.mm"
include "con3i.mm"
include "hashinf.mm"
include "syl2anr.mm"
include "wo.mm"
include "ianor.mm"
include "cn0.mm"
include "wnel.mm"
include "simprl.mm"
include "simprr.mm"
include "hashnfinnn0.mm"
include "ex.mm"
include "impcom.mm"
include "hashinfxadd.mm"
include "syl3anc.mm"
include "cxr.mm"
include "hashxrcl.mm"
include "adantl.mm"
include "xaddcom.mm"
include "jaoi.mm"
include "sylbi.mm"
include "imp.mm"
include "3adant3.mm"
include "pm2.61d.mm"

theorem hashunx
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W /\ ( A i^i B ) = (/) ) -> ( # ` ( A u. B ) ) = ( ( # ` A ) +e ( # ` B ) ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cA
    cB
    cin
    c0
    wceq
    #
    w3a
    cA
    cfn
    wcel
    #
    cB
    cfn
    wcel
    #
    wa
    #
    cA
    cB
    cun
    #
    chash
    cfv
    #
    cA
    chash
    cfv
    #
    cB
    chash
    cfv
    #
    cxad
    co
    #
    wceq
    #
    @2
    @0
    @5
    @11
    wi
    @1
    @5
    @2
    @11
    @5
    @2
    wa
    #
    @7
    @8
    @9
    caddc
    co
    #
    @10
    @3
    @4
    @2
    @7
    @13
    wceq
    cA
    cB
    hashun
    3expa
    @12
    @10
    @13
    @12
    @8
    cr
    wcel
    #
    @9
    cr
    wcel
    #
    wa
    #
    @10
    @13
    wceq
    @5
    @16
    @2
    @3
    @14
    @4
    @15
    @3
    @8
    cA
    hashcl
    nn0red
    @4
    @9
    cB
    hashcl
    nn0red
    anim12i
    adantr
    @8
    @9
    rexadd
    syl
    eqcomd
    eqtrd
    expcom
    3ad2ant3
    @0
    @1
    @5
    wn
    #
    @11
    wi
    @2
    @17
    @0
    @1
    wa
    #
    @11
    @17
    @18
    wa
    @7
    cpnf
    @10
    @18
    @6
    cvv
    wcel
    @6
    cfn
    wcel
    #
    wn
    @7
    cpnf
    wceq
    @17
    cA
    cB
    cV
    cW
    unexg
    @19
    @5
    cA
    cB
    unfir
    con3i
    @6
    cvv
    hashinf
    syl2anr
    @17
    @18
    cpnf
    @10
    wceq
    #
    @17
    @3
    wn
    #
    @4
    wn
    #
    wo
    @18
    @20
    wi
    #
    @3
    @4
    ianor
    @21
    @23
    @22
    @21
    @18
    @20
    @21
    @18
    wa
    #
    @10
    cpnf
    @24
    @0
    @1
    @8
    cn0
    wnel
    #
    @10
    cpnf
    wceq
    @21
    @0
    @1
    simprl
    @21
    @0
    @1
    simprr
    @18
    @21
    @25
    @0
    @21
    @25
    wi
    @1
    @0
    @21
    @25
    cA
    cV
    hashnfinnn0
    ex
    adantr
    impcom
    cA
    cB
    cV
    cW
    hashinfxadd
    syl3anc
    eqcomd
    ex
    @22
    @18
    @20
    @22
    @18
    wa
    #
    @10
    cpnf
    @26
    @10
    @9
    @8
    cxad
    co
    #
    cpnf
    @26
    @8
    cxr
    wcel
    #
    @9
    cxr
    wcel
    #
    wa
    #
    @10
    @27
    wceq
    @18
    @30
    @22
    @0
    @28
    @1
    @29
    cA
    cV
    hashxrcl
    cB
    cW
    hashxrcl
    anim12i
    adantl
    @8
    @9
    xaddcom
    syl
    @26
    @1
    @0
    @9
    cn0
    wnel
    #
    @27
    cpnf
    wceq
    @22
    @0
    @1
    simprr
    @22
    @0
    @1
    simprl
    @18
    @22
    @31
    @1
    @22
    @31
    wi
    @0
    @1
    @22
    @31
    cB
    cW
    hashnfinnn0
    ex
    adantl
    impcom
    cB
    cA
    cW
    cV
    hashinfxadd
    syl3anc
    eqtrd
    eqcomd
    ex
    jaoi
    sylbi
    imp
    eqtrd
    expcom
    3adant3
    pm2.61d
end
