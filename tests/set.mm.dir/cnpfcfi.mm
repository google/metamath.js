include "ctop.mm"
include "wcel.mm"
include "cfcls.mm"
include "co.mm"
include "ccnp.mm"
include "cfv.mm"
include "w3a.mm"
include "cv.mm"
include "wss.mm"
include "cflim.mm"
include "wa.mm"
include "cfcf.mm"
include "cuni.mm"
include "cfil.mm"
include "wrex.mm"
include "simp2.mm"
include "wb.mm"
include "eqid.mm"
include "fclsfil.mm"
include "3ad2ant2.mm"
include "fclsfnflim.mm"
include "syl.mm"
include "mpbid.mm"
include "cflf.mm"
include "ctopon.mm"
include "wf.mm"
include "simpl1.mm"
include "toptopon.mm"
include "sylib.mm"
include "simprl.mm"
include "cnpf.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "flfssfcf.mm"
include "syl3anc.mm"
include "cfm.mm"
include "cfbas.mm"
include "topopn.mm"
include "filfbas.mm"
include "fmfil.mm"
include "ad2antrl.mm"
include "simprrl.mm"
include "fmss.mm"
include "syl32anc.mm"
include "fclsss2.mm"
include "wceq.mm"
include "fcfval.mm"
include "3sstr4d.mm"
include "sstrd.mm"
include "simprrr.mm"
include "simpl3.mm"
include "cnpflfi.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "rexlimddv.mm"

theorem cnpfcfi
  let cA: class A
  let cF: class F
  let cJ: class J
  let cK: class K
  let cL: class L
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let cX: class X
  let cY: class Y


  assert |- ( ( K e. Top /\ A e. ( J fClus L ) /\ F e. ( ( J CnP K ) ` A ) ) -> ( F ` A ) e. ( ( K fClusf L ) ` F ) )

  proof
    cK
    ctop
    wcel
    #
    cA
    cJ
    cL
    cfcls
    co
    wcel
    #
    cF
    cA
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    w3a
    #
    cL
    vf
    cv
    #
    wss
    #
    cA
    cJ
    @4
    cflim
    co
    wcel
    #
    wa
    #
    cA
    cF
    cfv
    #
    cF
    cK
    cL
    cfcf
    co
    cfv
    #
    wcel
    vf
    cJ
    cuni
    #
    cfil
    cfv
    #
    @3
    @1
    @7
    vf
    @11
    wrex
    #
    @0
    @1
    @2
    simp2
    @3
    cL
    @11
    wcel
    #
    @1
    @12
    wb
    @1
    @0
    @13
    @2
    cA
    cL
    cJ
    @10
    @10
    eqid
    #
    fclsfil
    3ad2ant2
    #
    cA
    vf
    cL
    cJ
    @10
    fclsfnflim
    syl
    mpbid
    @3
    @4
    @11
    wcel
    #
    @7
    wa
    #
    wa
    #
    cF
    cK
    @4
    cflf
    co
    cfv
    #
    @9
    @8
    @18
    @19
    cF
    cK
    @4
    cfcf
    co
    cfv
    #
    @9
    @18
    cK
    cK
    cuni
    #
    ctopon
    cfv
    wcel
    #
    @16
    @10
    @21
    cF
    wf
    #
    @19
    @20
    wss
    @18
    @0
    @22
    @0
    @1
    @2
    @17
    simpl1
    #
    cK
    @21
    @21
    eqid
    #
    toptopon
    sylib
    #
    @3
    @16
    @7
    simprl
    #
    @3
    @23
    @17
    @2
    @0
    @23
    @1
    cA
    cF
    cJ
    cK
    @10
    @21
    @14
    @25
    cnpf
    3ad2ant3
    adantr
    #
    cF
    cK
    @4
    @21
    @10
    flfssfcf
    syl3anc
    @18
    cK
    @4
    @21
    cF
    cfm
    co
    #
    cfv
    #
    cfcls
    co
    #
    cK
    cL
    @29
    cfv
    #
    cfcls
    co
    #
    @20
    @9
    @18
    @22
    @32
    @21
    cfil
    cfv
    wcel
    #
    @32
    @30
    wss
    #
    @31
    @33
    wss
    @26
    @18
    @21
    cK
    wcel
    #
    cL
    @10
    cfbas
    cfv
    #
    wcel
    #
    @23
    @34
    @18
    @0
    @36
    @24
    cK
    @21
    @25
    topopn
    syl
    #
    @18
    @13
    @38
    @3
    @13
    @17
    @15
    adantr
    #
    cL
    @10
    filfbas
    syl
    #
    @28
    cK
    cL
    cF
    @21
    @10
    fmfil
    syl3anc
    @18
    @36
    @38
    @4
    @37
    wcel
    #
    @23
    @5
    @35
    @39
    @41
    @16
    @42
    @3
    @7
    @4
    @10
    filfbas
    ad2antrl
    @28
    @3
    @16
    @5
    @6
    simprrl
    cK
    cL
    @4
    cF
    @21
    @10
    fmss
    syl32anc
    @32
    @30
    cK
    @21
    fclsss2
    syl3anc
    @18
    @22
    @16
    @23
    @20
    @31
    wceq
    @26
    @27
    @28
    cF
    cK
    @4
    @21
    @10
    fcfval
    syl3anc
    @18
    @22
    @13
    @23
    @9
    @33
    wceq
    @26
    @40
    @28
    cF
    cK
    cL
    @21
    @10
    fcfval
    syl3anc
    3sstr4d
    sstrd
    @18
    @6
    @2
    @8
    @19
    wcel
    @3
    @16
    @5
    @6
    simprrr
    @0
    @1
    @2
    @17
    simpl3
    cA
    cF
    cJ
    cK
    @4
    cnpflfi
    syl2anc
    sseldd
    rexlimddv
end
