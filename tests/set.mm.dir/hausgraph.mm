include "cha.mm"
include "wcel.mm"
include "ccn.mm"
include "co.mm"
include "wa.mm"
include "c1st.mm"
include "cuni.mm"
include "cxp.mm"
include "cres.mm"
include "ccom.mm"
include "c2nd.mm"
include "cin.mm"
include "cdm.mm"
include "ctx.mm"
include "ccld.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "crab.mm"
include "wfn.mm"
include "wf.mm"
include "f1stres.mm"
include "ffn.mm"
include "ax-mp.mm"
include "fvco2.mm"
include "mpan.mm"
include "adantl.mm"
include "fvres.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "eqeq12d.mm"
include "rabbidva.mm"
include "eqid.mm"
include "cnf.mm"
include "fco.mm"
include "sylancl.mm"
include "syl.mm"
include "f2ndres.mm"
include "fndmin.mm"
include "fgraphxp.mm"
include "3eqtr4rd.mm"
include "simpl.mm"
include "ctopon.mm"
include "ctop.mm"
include "cntop1.mm"
include "toptopon.mm"
include "sylib.mm"
include "haustop.mm"
include "tx1cn.mm"
include "syl2anc.mm"
include "cnco.mm"
include "sylancom.mm"
include "tx2cn.mm"
include "hauseqlcld.mm"
include "eqeltrd.mm"

theorem hausgraph
  let cF: class F
  let cJ: class J
  let cK: class K
  let va: setvar a


  assert |- ( ( K e. Haus /\ F e. ( J Cn K ) ) -> F e. ( Clsd ` ( J tX K ) ) )

  proof
    cK
    cha
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
    cF
    cF
    c1st
    cJ
    cuni
    #
    cK
    cuni
    #
    cxp
    #
    cres
    #
    ccom
    #
    c2nd
    @5
    cres
    #
    cin
    cdm
    #
    cJ
    cK
    ctx
    co
    #
    ccld
    cfv
    @2
    va
    cv
    #
    @7
    cfv
    #
    @11
    @8
    cfv
    #
    wceq
    #
    va
    @5
    crab
    #
    @11
    c1st
    cfv
    #
    cF
    cfv
    #
    @11
    c2nd
    cfv
    #
    wceq
    #
    va
    @5
    crab
    #
    @9
    cF
    @2
    @14
    @19
    va
    @5
    @2
    @11
    @5
    wcel
    #
    wa
    #
    @12
    @17
    @13
    @18
    @22
    @12
    @11
    @6
    cfv
    #
    cF
    cfv
    #
    @17
    @21
    @12
    @24
    wceq
    #
    @2
    @6
    @5
    wfn
    #
    @21
    @25
    @5
    @3
    @6
    wf
    #
    @26
    @3
    @4
    f1stres
    #
    @5
    @3
    @6
    ffn
    ax-mp
    @5
    cF
    @6
    @11
    fvco2
    mpan
    adantl
    @21
    @24
    @17
    wceq
    @2
    @21
    @23
    @16
    cF
    @11
    @5
    c1st
    fvres
    fveq2d
    adantl
    eqtrd
    @21
    @13
    @18
    wceq
    @2
    @11
    @5
    c2nd
    fvres
    adantl
    eqeq12d
    rabbidva
    @2
    @7
    @5
    wfn
    #
    @8
    @5
    wfn
    #
    @9
    @15
    wceq
    @2
    @5
    @4
    @7
    wf
    #
    @29
    @2
    @3
    @4
    cF
    wf
    #
    @27
    @31
    @1
    @32
    @0
    cF
    cJ
    cK
    @3
    @4
    @3
    eqid
    #
    @4
    eqid
    #
    cnf
    adantl
    #
    @28
    @5
    @3
    @4
    cF
    @6
    fco
    sylancl
    @5
    @4
    @7
    ffn
    syl
    @5
    @4
    @8
    wf
    @30
    @3
    @4
    f2ndres
    @5
    @4
    @8
    ffn
    ax-mp
    va
    @5
    @7
    @8
    fndmin
    sylancl
    @2
    @32
    cF
    @20
    wceq
    @35
    va
    @3
    @4
    cF
    fgraphxp
    syl
    3eqtr4rd
    @2
    @7
    @8
    @10
    cK
    @0
    @1
    simpl
    #
    @0
    @1
    @6
    @10
    cJ
    ccn
    co
    wcel
    #
    @7
    @10
    cK
    ccn
    co
    #
    wcel
    @2
    cJ
    @3
    ctopon
    cfv
    wcel
    #
    cK
    @4
    ctopon
    cfv
    wcel
    #
    @37
    @2
    cJ
    ctop
    wcel
    #
    @39
    @1
    @41
    @0
    cF
    cJ
    cK
    cntop1
    adantl
    cJ
    @3
    @33
    toptopon
    sylib
    #
    @2
    cK
    ctop
    wcel
    #
    @40
    @2
    @0
    @43
    @36
    cK
    haustop
    syl
    cK
    @4
    @34
    toptopon
    sylib
    #
    cJ
    cK
    @3
    @4
    tx1cn
    syl2anc
    @6
    cF
    @10
    cJ
    cK
    cnco
    sylancom
    @2
    @39
    @40
    @8
    @38
    wcel
    @42
    @44
    cJ
    cK
    @3
    @4
    tx2cn
    syl2anc
    hauseqlcld
    eqeltrd
end
