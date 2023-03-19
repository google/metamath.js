include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cvsca.mm"
include "cfv.mm"
include "ccom.mm"
include "csca.mm"
include "cbs.mm"
include "eqid.mm"
include "clmod.mm"
include "lmhmlmod1.mm"
include "adantl.mm"
include "lmhmlmod2.mm"
include "adantr.mm"
include "lmhmsca.mm"
include "sylan9eq.mm"
include "cghm.mm"
include "lmghm.mm"
include "ghmco.mm"
include "syl2an.mm"
include "cv.mm"
include "wceq.mm"
include "simplr.mm"
include "simprl.mm"
include "simprr.mm"
include "lmhmlin.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "simpll.mm"
include "ad2antlr.mm"
include "eleqtrrd.mm"
include "wf.mm"
include "lmhmf.mm"
include "ffvelrnda.mm"
include "adantrl.mm"
include "eqtrd.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "lmodvscl.mm"
include "fvco2.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "islmhmd.mm"

theorem lmhmco
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let cO: class O
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F e. ( N LMHom O ) /\ G e. ( M LMHom N ) ) -> ( F o. G ) e. ( M LMHom O ) )

  proof
    cF
    cN
    cO
    clmhm
    co
    wcel
    #
    cG
    cM
    cN
    clmhm
    co
    wcel
    #
    wa
    #
    vx
    vy
    cM
    cO
    cM
    cvsca
    cfv
    #
    cO
    cvsca
    cfv
    #
    cF
    cG
    ccom
    #
    cO
    csca
    cfv
    #
    cM
    csca
    cfv
    #
    @7
    cbs
    cfv
    #
    cM
    cbs
    cfv
    #
    @9
    eqid
    #
    @3
    eqid
    #
    @4
    eqid
    #
    @7
    eqid
    #
    @6
    eqid
    #
    @8
    eqid
    #
    @1
    cM
    clmod
    wcel
    #
    @0
    cM
    cN
    cG
    lmhmlmod1
    #
    adantl
    @0
    cO
    clmod
    wcel
    @1
    cN
    cO
    cF
    lmhmlmod2
    adantr
    @0
    @1
    @6
    cN
    csca
    cfv
    #
    @7
    cN
    cO
    cF
    @18
    @6
    @18
    eqid
    #
    @14
    lmhmsca
    cM
    cN
    cG
    @7
    @18
    @13
    @19
    lmhmsca
    #
    sylan9eq
    @0
    cF
    cN
    cO
    cghm
    co
    wcel
    cG
    cM
    cN
    cghm
    co
    wcel
    @5
    cM
    cO
    cghm
    co
    wcel
    @1
    cN
    cO
    cF
    lmghm
    cM
    cN
    cG
    lmghm
    cM
    cN
    cO
    cF
    cG
    ghmco
    syl2an
    @2
    vx
    cv
    #
    @8
    wcel
    #
    vy
    cv
    #
    @9
    wcel
    #
    wa
    #
    wa
    #
    @21
    @23
    @3
    co
    #
    cG
    cfv
    #
    cF
    cfv
    #
    @21
    @23
    cG
    cfv
    #
    cF
    cfv
    #
    @4
    co
    #
    @27
    @5
    cfv
    #
    @21
    @23
    @5
    cfv
    #
    @4
    co
    @26
    @29
    @21
    @30
    cN
    cvsca
    cfv
    #
    co
    #
    cF
    cfv
    #
    @32
    @26
    @28
    @36
    cF
    @26
    @1
    @22
    @24
    @28
    @36
    wceq
    @0
    @1
    @25
    simplr
    @2
    @22
    @24
    simprl
    #
    @2
    @22
    @24
    simprr
    #
    @8
    cM
    cN
    @3
    @35
    @9
    cG
    @7
    @21
    @23
    @13
    @15
    @10
    @11
    @35
    eqid
    #
    lmhmlin
    syl3anc
    fveq2d
    @26
    @0
    @21
    @18
    cbs
    cfv
    #
    wcel
    @30
    cN
    cbs
    cfv
    #
    wcel
    #
    @37
    @32
    wceq
    @0
    @1
    @25
    simpll
    @26
    @21
    @8
    @41
    @38
    @1
    @41
    @8
    wceq
    @0
    @25
    @1
    @18
    @7
    cbs
    @20
    fveq2d
    ad2antlr
    eleqtrrd
    @2
    @24
    @43
    @22
    @2
    @9
    @42
    @23
    cG
    @1
    @9
    @42
    cG
    wf
    #
    @0
    @9
    @42
    cM
    cN
    cG
    @10
    @42
    eqid
    #
    lmhmf
    adantl
    #
    ffvelrnda
    adantrl
    @41
    cN
    cO
    @35
    @4
    @42
    cF
    @18
    @21
    @30
    @19
    @41
    eqid
    @45
    @40
    @12
    lmhmlin
    syl3anc
    eqtrd
    @26
    cG
    @9
    wfn
    #
    @27
    @9
    wcel
    #
    @33
    @29
    wceq
    @2
    @47
    @25
    @2
    @44
    @47
    @46
    @9
    @42
    cG
    ffn
    syl
    adantr
    #
    @26
    @16
    @22
    @24
    @48
    @1
    @16
    @0
    @25
    @17
    ad2antlr
    @38
    @39
    @21
    @3
    @7
    @8
    @9
    cM
    @23
    @10
    @13
    @11
    @15
    lmodvscl
    syl3anc
    @9
    cF
    cG
    @27
    fvco2
    syl2anc
    @26
    @34
    @31
    @21
    @4
    @26
    @47
    @24
    @34
    @31
    wceq
    @49
    @39
    @9
    cF
    cG
    @23
    fvco2
    syl2anc
    oveq2d
    3eqtr4d
    islmhmd
end
