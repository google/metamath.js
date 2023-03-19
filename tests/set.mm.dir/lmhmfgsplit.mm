include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "clfig.mm"
include "w3a.mm"
include "cv.mm"
include "cfn.mm"
include "clspn.mm"
include "cfv.mm"
include "crn.mm"
include "wceq.mm"
include "wa.mm"
include "cpw.mm"
include "wrex.mm"
include "simp3.mm"
include "clmod.mm"
include "clss.mm"
include "wb.mm"
include "lmhmlmod2.mm"
include "3ad2ant1.mm"
include "lmhmrnlss.mm"
include "eqid.mm"
include "islssfg.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "cima.mm"
include "cbs.mm"
include "cin.mm"
include "wfn.mm"
include "wss.mm"
include "wf.mm"
include "simpl1.mm"
include "lmhmf.mm"
include "ffn.mm"
include "3syl.mm"
include "elpwi.mm"
include "ad2antrl.mm"
include "simprrl.mm"
include "fipreima.mm"
include "syl3anc.mm"
include "clsm.mm"
include "cress.mm"
include "simpll1.mm"
include "lmhmlmod1.mm"
include "ad2antrr.mm"
include "inss1.mm"
include "sseli.mm"
include "syl.mm"
include "lspcl.mm"
include "lmhmlsp.mm"
include "fveq2.mm"
include "ad2antll.mm"
include "simp2rr.mm"
include "3expa.mm"
include "3eqtrd.mm"
include "kercvrlsm.mm"
include "oveq2d.mm"
include "ressid.mm"
include "eqtr2d.mm"
include "lmhmkerlss.mm"
include "simpll2.mm"
include "inss2.mm"
include "islssfgi.mm"
include "lsmfgcl.mm"
include "eqeltrd.mm"
include "rexlimddv.mm"

theorem lmhmfgsplit
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cK: class K
  let cV: class V
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  assume lmhmfgsplit.z: |- .0. = ( 0g ` T )
  assume lmhmfgsplit.k: |- K = ( `' F " { .0. } )
  assume lmhmfgsplit.u: |- U = ( S |`s K )
  assume lmhmfgsplit.v: |- V = ( T |`s ran F )


  assert |- ( ( F e. ( S LMHom T ) /\ U e. LFinGen /\ V e. LFinGen ) -> S e. LFinGen )

  proof
    cF
    cS
    cT
    clmhm
    co
    wcel
    #
    cU
    clfig
    wcel
    #
    cV
    clfig
    wcel
    #
    w3a
    #
    va
    cv
    #
    cfn
    wcel
    #
    @4
    cT
    clspn
    cfv
    #
    cfv
    #
    cF
    crn
    #
    wceq
    #
    wa
    #
    cS
    clfig
    wcel
    #
    va
    @8
    cpw
    #
    @3
    @2
    @10
    va
    @12
    wrex
    #
    @0
    @1
    @2
    simp3
    @3
    cT
    clmod
    wcel
    #
    @8
    cT
    clss
    cfv
    #
    wcel
    #
    @2
    @13
    wb
    @0
    @1
    @14
    @2
    cS
    cT
    cF
    lmhmlmod2
    3ad2ant1
    @0
    @1
    @16
    @2
    cS
    cT
    cF
    lmhmrnlss
    3ad2ant1
    @15
    @8
    @6
    cT
    cV
    va
    lmhmfgsplit.v
    @15
    eqid
    @6
    eqid
    #
    islssfg
    syl2anc
    mpbid
    @3
    @4
    @12
    wcel
    #
    @10
    wa
    #
    wa
    #
    cF
    vb
    cv
    #
    cima
    #
    @4
    wceq
    #
    @11
    vb
    cS
    cbs
    cfv
    #
    cpw
    #
    cfn
    cin
    #
    @20
    cF
    @24
    wfn
    #
    @4
    @8
    wss
    #
    @5
    @23
    vb
    @26
    wrex
    @20
    @0
    @24
    cT
    cbs
    cfv
    #
    cF
    wf
    @27
    @0
    @1
    @2
    @19
    simpl1
    @24
    @29
    cS
    cT
    cF
    @24
    eqid
    #
    @29
    eqid
    lmhmf
    @24
    @29
    cF
    ffn
    3syl
    @18
    @28
    @3
    @10
    @4
    @8
    elpwi
    ad2antrl
    @3
    @18
    @5
    @9
    simprrl
    @4
    @24
    cF
    vb
    fipreima
    syl3anc
    @20
    @21
    @26
    wcel
    #
    @23
    wa
    #
    wa
    #
    cS
    cS
    cK
    @21
    cS
    clspn
    cfv
    #
    cfv
    #
    cS
    clsm
    cfv
    #
    co
    #
    cress
    co
    #
    clfig
    @33
    @38
    cS
    @24
    cress
    co
    #
    cS
    @33
    @37
    @24
    cS
    cress
    @33
    @24
    @35
    @36
    cS
    cT
    cS
    clss
    cfv
    #
    cF
    cK
    c.0
    @40
    eqid
    #
    @36
    eqid
    #
    lmhmfgsplit.z
    lmhmfgsplit.k
    @30
    @0
    @1
    @2
    @19
    @32
    simpll1
    #
    @33
    cS
    clmod
    wcel
    #
    @21
    @24
    wss
    #
    @35
    @40
    wcel
    @3
    @44
    @19
    @32
    @0
    @1
    @44
    @2
    cS
    cT
    cF
    lmhmlmod1
    3ad2ant1
    #
    ad2antrr
    #
    @31
    @45
    @20
    @23
    @31
    @21
    @25
    wcel
    @45
    @26
    @25
    @21
    @25
    cfn
    inss1
    sseli
    @21
    @24
    elpwi
    syl
    ad2antrl
    #
    @40
    @21
    @34
    @24
    cS
    @30
    @41
    @34
    eqid
    #
    lspcl
    syl2anc
    #
    @33
    cF
    @35
    cima
    #
    @22
    @6
    cfv
    #
    @7
    @8
    @33
    @0
    @45
    @51
    @52
    wceq
    @43
    @48
    cS
    cT
    @21
    cF
    @34
    @6
    @24
    @30
    @49
    @17
    lmhmlsp
    syl2anc
    @23
    @52
    @7
    wceq
    @20
    @31
    @22
    @4
    @6
    fveq2
    ad2antll
    @3
    @19
    @32
    @9
    @5
    @9
    @18
    @3
    @32
    simp2rr
    3expa
    3eqtrd
    kercvrlsm
    oveq2d
    @3
    @39
    cS
    wceq
    #
    @19
    @32
    @3
    @44
    @53
    @46
    @24
    cS
    clmod
    @30
    ressid
    syl
    ad2antrr
    eqtr2d
    @33
    cK
    @35
    cU
    @36
    @40
    cS
    @35
    cress
    co
    #
    @38
    cS
    @41
    @42
    lmhmfgsplit.u
    @54
    eqid
    #
    @38
    eqid
    @47
    @3
    cK
    @40
    wcel
    #
    @19
    @32
    @0
    @1
    @56
    @2
    cS
    cT
    @40
    cF
    cK
    c.0
    lmhmfgsplit.k
    lmhmfgsplit.z
    @41
    lmhmkerlss
    3ad2ant1
    ad2antrr
    @50
    @0
    @1
    @2
    @19
    @32
    simpll2
    @33
    @44
    @45
    @21
    cfn
    wcel
    #
    @54
    clfig
    wcel
    @47
    @48
    @31
    @57
    @20
    @23
    @26
    cfn
    @21
    @25
    cfn
    inss2
    sseli
    ad2antrl
    @21
    @34
    @24
    cS
    @54
    @49
    @30
    @55
    islssfgi
    syl3anc
    lsmfgcl
    eqeltrd
    rexlimddv
    rexlimddv
end
