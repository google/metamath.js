include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cvsca.mm"
include "cfv.mm"
include "cof.mm"
include "csca.mm"
include "cbs.mm"
include "eqid.mm"
include "clmod.mm"
include "lmhmlmod1.mm"
include "adantr.mm"
include "lmhmlmod2.mm"
include "wceq.mm"
include "lmhmsca.mm"
include "cabl.mm"
include "cghm.mm"
include "lmodabl.mm"
include "syl.mm"
include "lmghm.mm"
include "adantl.mm"
include "ghmplusg.mm"
include "syl3anc.mm"
include "cv.mm"
include "simpll.mm"
include "simprl.mm"
include "simprr.mm"
include "lmhmlin.mm"
include "simplr.mm"
include "oveq12d.mm"
include "ad2antrr.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "wf.mm"
include "lmhmf.mm"
include "ffvelrnd.mm"
include "ad2antlr.mm"
include "lmodvsdi.mm"
include "syl13anc.mm"
include "eqtr4d.mm"
include "wfn.mm"
include "cvv.mm"
include "ffn.mm"
include "fvexd.mm"
include "lmodvscl.mm"
include "fnfvof.mm"
include "syl22anc.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "islmhmd.mm"

theorem lmhmplusg
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  assume lmhmplusg.p: |- .+ = ( +g ` N )


  assert |- ( ( F e. ( M LMHom N ) /\ G e. ( M LMHom N ) ) -> ( F oF .+ G ) e. ( M LMHom N ) )

  proof
    cF
    cM
    cN
    clmhm
    co
    #
    wcel
    #
    cG
    @0
    wcel
    #
    wa
    #
    vx
    vy
    cM
    cN
    cM
    cvsca
    cfv
    #
    cN
    cvsca
    cfv
    #
    cF
    cG
    c.pl
    cof
    co
    #
    cN
    csca
    cfv
    #
    cM
    csca
    cfv
    #
    @8
    cbs
    cfv
    #
    cM
    cbs
    cfv
    #
    @10
    eqid
    #
    @4
    eqid
    #
    @5
    eqid
    #
    @8
    eqid
    #
    @7
    eqid
    #
    @9
    eqid
    #
    @1
    cM
    clmod
    wcel
    #
    @2
    cM
    cN
    cF
    lmhmlmod1
    #
    adantr
    @1
    cN
    clmod
    wcel
    #
    @2
    cM
    cN
    cF
    lmhmlmod2
    #
    adantr
    #
    @1
    @7
    @8
    wceq
    @2
    cM
    cN
    cF
    @8
    @7
    @14
    @15
    lmhmsca
    #
    adantr
    @3
    cN
    cabl
    wcel
    #
    cF
    cM
    cN
    cghm
    co
    #
    wcel
    #
    cG
    @24
    wcel
    #
    @6
    @24
    wcel
    @3
    @19
    @23
    @21
    cN
    lmodabl
    syl
    @1
    @25
    @2
    cM
    cN
    cF
    lmghm
    adantr
    @2
    @26
    @1
    cM
    cN
    cG
    lmghm
    adantl
    c.pl
    cF
    cG
    cM
    cN
    lmhmplusg.p
    ghmplusg
    syl3anc
    @3
    vx
    cv
    #
    @9
    wcel
    #
    vy
    cv
    #
    @10
    wcel
    #
    wa
    #
    wa
    #
    @27
    @29
    @4
    co
    #
    cF
    cfv
    #
    @33
    cG
    cfv
    #
    c.pl
    co
    #
    @27
    @29
    cF
    cfv
    #
    @29
    cG
    cfv
    #
    c.pl
    co
    #
    @5
    co
    #
    @33
    @6
    cfv
    #
    @27
    @29
    @6
    cfv
    #
    @5
    co
    @32
    @36
    @27
    @37
    @5
    co
    #
    @27
    @38
    @5
    co
    #
    c.pl
    co
    #
    @40
    @32
    @34
    @43
    @35
    @44
    c.pl
    @32
    @1
    @28
    @30
    @34
    @43
    wceq
    @1
    @2
    @31
    simpll
    @3
    @28
    @30
    simprl
    #
    @3
    @28
    @30
    simprr
    #
    @9
    cM
    cN
    @4
    @5
    @10
    cF
    @8
    @27
    @29
    @14
    @16
    @11
    @12
    @13
    lmhmlin
    syl3anc
    @32
    @2
    @28
    @30
    @35
    @44
    wceq
    @1
    @2
    @31
    simplr
    @46
    @47
    @9
    cM
    cN
    @4
    @5
    @10
    cG
    @8
    @27
    @29
    @14
    @16
    @11
    @12
    @13
    lmhmlin
    syl3anc
    oveq12d
    @32
    @19
    @27
    @7
    cbs
    cfv
    #
    wcel
    @37
    cN
    cbs
    cfv
    #
    wcel
    @38
    @49
    wcel
    @40
    @45
    wceq
    @1
    @19
    @2
    @31
    @20
    ad2antrr
    @32
    @27
    @9
    @48
    @46
    @1
    @48
    @9
    wceq
    @2
    @31
    @1
    @7
    @8
    cbs
    @22
    fveq2d
    ad2antrr
    eleqtrrd
    @32
    @10
    @49
    @29
    cF
    @1
    @10
    @49
    cF
    wf
    #
    @2
    @31
    @10
    @49
    cM
    cN
    cF
    @11
    @49
    eqid
    #
    lmhmf
    ad2antrr
    #
    @47
    ffvelrnd
    @32
    @10
    @49
    @29
    cG
    @2
    @10
    @49
    cG
    wf
    #
    @1
    @31
    @10
    @49
    cM
    cN
    cG
    @11
    @51
    lmhmf
    ad2antlr
    #
    @47
    ffvelrnd
    c.pl
    @27
    @5
    @7
    @48
    @49
    cN
    @37
    @38
    @51
    lmhmplusg.p
    @15
    @13
    @48
    eqid
    lmodvsdi
    syl13anc
    eqtr4d
    @32
    cF
    @10
    wfn
    #
    cG
    @10
    wfn
    #
    @10
    cvv
    wcel
    #
    @33
    @10
    wcel
    #
    @41
    @36
    wceq
    @32
    @50
    @55
    @52
    @10
    @49
    cF
    ffn
    syl
    #
    @32
    @53
    @56
    @54
    @10
    @49
    cG
    ffn
    syl
    #
    @32
    cM
    cbs
    fvexd
    #
    @32
    @17
    @28
    @30
    @58
    @1
    @17
    @2
    @31
    @18
    ad2antrr
    @46
    @47
    @27
    @4
    @8
    @9
    @10
    cM
    @29
    @11
    @14
    @12
    @16
    lmodvscl
    syl3anc
    @10
    c.pl
    cF
    cG
    cvv
    @33
    fnfvof
    syl22anc
    @32
    @42
    @39
    @27
    @5
    @32
    @55
    @56
    @57
    @30
    @42
    @39
    wceq
    @59
    @60
    @61
    @47
    @10
    c.pl
    cF
    cG
    cvv
    @29
    fnfvof
    syl22anc
    oveq2d
    3eqtr4d
    islmhmd
end
