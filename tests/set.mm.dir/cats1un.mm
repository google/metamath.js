include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "csn.mm"
include "cun.mm"
include "cs1.mm"
include "cconcat.mm"
include "cop.mm"
include "wf.mm"
include "ccatws1cl.mm"
include "wrdf.mm"
include "syl.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "ccatws1len.mm"
include "adantr.mm"
include "oveq2d.mm"
include "cuz.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "fzosplitsn.mm"
include "eqtrd.mm"
include "feq2d.mm"
include "mpbid.mm"
include "ffnd.mm"
include "cin.mm"
include "c0.mm"
include "eqid.mm"
include "fsng.mm"
include "mpbiri.mm"
include "sylan.mm"
include "wn.mm"
include "fzonel.mm"
include "a1i.mm"
include "disjsn.mm"
include "sylibr.mm"
include "fun.mm"
include "syl21anc.mm"
include "cv.mm"
include "wo.mm"
include "elun.mm"
include "ccats1val1.mm"
include "3expa.mm"
include "wne.mm"
include "simpr.mm"
include "nelne2.mm"
include "sylancl.mm"
include "necomd.mm"
include "fvunsn.mm"
include "eqtr4d.mm"
include "cvv.mm"
include "cdm.mm"
include "fvexd.mm"
include "elex.mm"
include "adantl.mm"
include "fdm.mm"
include "eleq2d.mm"
include "mtbiri.mm"
include "fsnunfv.mm"
include "syl3anc.mm"
include "simpl.mm"
include "s1cl.mm"
include "cn.mm"
include "s1len.mm"
include "1nn.mm"
include "eqeltri.mm"
include "lbfzo0.mm"
include "ccatval3.mm"
include "s1fv.mm"
include "nn0cnd.mm"
include "addid2d.mm"
include "fveq2d.mm"
include "3eqtr2rd.mm"
include "elsni.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "eqfnfvd.mm"

theorem cats1un
  let cA: class A
  let cB: class B
  let cX: class X
  let vx: setvar x


  assert |- ( ( A e. Word X /\ B e. X ) -> ( A ++ <" B "> ) = ( A u. { <. ( # ` A ) , B >. } ) )

  proof
    cA
    cX
    cword
    #
    wcel
    #
    cB
    cX
    wcel
    #
    wa
    #
    vx
    cc0
    cA
    chash
    cfv
    #
    cfzo
    co
    #
    @4
    csn
    #
    cun
    #
    cA
    cB
    cs1
    #
    cconcat
    co
    #
    cA
    @4
    cB
    cop
    csn
    #
    cun
    #
    @3
    @7
    cX
    @9
    @3
    cc0
    @9
    chash
    cfv
    #
    cfzo
    co
    #
    cX
    @9
    wf
    #
    @7
    cX
    @9
    wf
    @3
    @9
    @0
    wcel
    @14
    cX
    cA
    cB
    ccatws1cl
    cX
    @9
    wrdf
    syl
    @3
    @13
    @7
    cX
    @9
    @3
    @13
    cc0
    @4
    c1
    caddc
    co
    #
    cfzo
    co
    #
    @7
    @3
    @12
    @15
    cc0
    cfzo
    @1
    @12
    @15
    wceq
    @2
    cX
    cA
    cB
    ccatws1len
    adantr
    oveq2d
    @3
    @4
    cc0
    cuz
    cfv
    #
    wcel
    @16
    @7
    wceq
    @3
    @4
    cn0
    @17
    @1
    @4
    cn0
    wcel
    #
    @2
    cX
    cA
    lencl
    #
    adantr
    #
    nn0uz
    syl6eleq
    cc0
    @4
    fzosplitsn
    syl
    eqtrd
    feq2d
    mpbid
    ffnd
    @3
    @7
    cX
    cB
    csn
    #
    cun
    #
    @11
    @3
    @5
    cX
    cA
    wf
    #
    @6
    @21
    @10
    wf
    #
    @5
    @6
    cin
    c0
    wceq
    #
    @7
    @22
    @11
    wf
    @1
    @23
    @2
    cX
    cA
    wrdf
    adantr
    #
    @1
    @18
    @2
    @24
    @19
    @18
    @2
    wa
    @24
    @10
    @10
    wceq
    @10
    eqid
    @4
    cB
    cn0
    cX
    @10
    fsng
    mpbiri
    sylan
    @3
    @4
    @5
    wcel
    #
    wn
    #
    @25
    @28
    @3
    cc0
    @4
    fzonel
    #
    a1i
    @5
    @4
    disjsn
    sylibr
    @5
    @6
    cX
    @21
    cA
    @10
    fun
    syl21anc
    ffnd
    vx
    cv
    #
    @7
    wcel
    @3
    @30
    @5
    wcel
    #
    @30
    @6
    wcel
    #
    wo
    @30
    @9
    cfv
    #
    @30
    @11
    cfv
    #
    wceq
    #
    @30
    @5
    @6
    elun
    @3
    @31
    @35
    @32
    @3
    @31
    wa
    #
    @33
    @30
    cA
    cfv
    #
    @34
    @1
    @2
    @31
    @33
    @37
    wceq
    cB
    @30
    cX
    cA
    ccats1val1
    3expa
    @36
    @4
    @30
    wne
    @34
    @37
    wceq
    @36
    @30
    @4
    @36
    @31
    @28
    @30
    @4
    wne
    @3
    @31
    simpr
    @29
    @30
    @4
    @5
    nelne2
    sylancl
    necomd
    cA
    @4
    cB
    @30
    fvunsn
    syl
    eqtr4d
    @3
    @32
    @35
    @3
    @35
    @32
    @4
    @9
    cfv
    #
    @4
    @11
    cfv
    #
    wceq
    @3
    @39
    cB
    cc0
    @4
    caddc
    co
    #
    @9
    cfv
    #
    @38
    @3
    @4
    cvv
    wcel
    cB
    cvv
    wcel
    #
    @4
    cA
    cdm
    #
    wcel
    #
    wn
    @39
    cB
    wceq
    @3
    cA
    chash
    fvexd
    @2
    @42
    @1
    cB
    cX
    elex
    adantl
    @3
    @44
    @27
    @29
    @3
    @43
    @5
    @4
    @3
    @23
    @43
    @5
    wceq
    @26
    @5
    cX
    cA
    fdm
    syl
    eleq2d
    mtbiri
    cA
    cvv
    cvv
    @4
    cB
    fsnunfv
    syl3anc
    @3
    @41
    cc0
    @8
    cfv
    #
    cB
    @3
    @1
    @8
    @0
    wcel
    #
    cc0
    cc0
    @8
    chash
    cfv
    #
    cfzo
    co
    wcel
    #
    @41
    @45
    wceq
    @1
    @2
    simpl
    @2
    @46
    @1
    cB
    cX
    s1cl
    adantl
    @3
    @47
    cn
    wcel
    #
    @48
    @49
    @3
    @47
    c1
    cn
    cB
    s1len
    1nn
    eqeltri
    a1i
    @47
    lbfzo0
    sylibr
    cX
    cA
    @8
    cc0
    ccatval3
    syl3anc
    @2
    @45
    cB
    wceq
    @1
    cB
    cX
    s1fv
    adantl
    eqtrd
    @3
    @40
    @4
    @9
    @3
    @4
    @3
    @4
    @20
    nn0cnd
    addid2d
    fveq2d
    3eqtr2rd
    @32
    @33
    @38
    @34
    @39
    @32
    @30
    @4
    @9
    @30
    @4
    elsni
    #
    fveq2d
    @32
    @30
    @4
    @11
    @50
    fveq2d
    eqeq12d
    syl5ibrcom
    imp
    jaodan
    sylan2b
    eqfnfvd
end
