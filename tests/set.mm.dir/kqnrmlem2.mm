include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ckq.mm"
include "cnrm.mm"
include "wa.mm"
include "ctop.mm"
include "cv.mm"
include "wss.mm"
include "ccl.mm"
include "wrex.mm"
include "ccld.mm"
include "cpw.mm"
include "cin.mm"
include "wral.mm"
include "topontop.mm"
include "adantr.mm"
include "cima.mm"
include "simplr.mm"
include "simpll.mm"
include "simprl.mm"
include "kqopn.mm"
include "syl2anc.mm"
include "inss1.mm"
include "simprr.mm"
include "sseldi.mm"
include "kqcld.mm"
include "inss2.mm"
include "elpwi.mm"
include "imass2.mm"
include "3syl.mm"
include "nrmsep3.mm"
include "syl13anc.mm"
include "ccnv.mm"
include "ccn.mm"
include "co.mm"
include "simplll.mm"
include "kqid.mm"
include "syl.mm"
include "cnima.mm"
include "simprrl.mm"
include "wfun.mm"
include "cdm.mm"
include "wb.mm"
include "wfn.mm"
include "kqffn.mm"
include "fnfun.mm"
include "cuni.mm"
include "eqid.mm"
include "cldss.mm"
include "wceq.mm"
include "fndm.mm"
include "toponuni.mm"
include "eqtrd.mm"
include "sseqtr4d.mm"
include "funimass3.mm"
include "mpbid.mm"
include "crn.mm"
include "kqtopon.mm"
include "elssuni.mm"
include "ad2antrl.mm"
include "clscld.mm"
include "cnclima.mm"
include "sscls.mm"
include "clsss2.mm"
include "simprrr.mm"
include "kqsat.mm"
include "sseqtrd.mm"
include "sstrd.mm"
include "sseq2.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rexlimddv.mm"
include "ralrimivva.mm"
include "isnrm.mm"
include "sylanbrc.mm"

theorem kqnrmlem2
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cJ: class J
  let cX: class X
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vj: setvar j
  let vu: setvar u
  let vv: setvar v
  let wph: wff ph
  let cU: class U
  let cV: class V
  assume kqval.2: |- F = ( x e. X |-> { y e. J | x e. y } )

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint X x
  disjoint X y
  disjoint m n
  disjoint m o
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n o
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint o w
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint A o
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B m
  disjoint B n
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint a b
  disjoint a j
  disjoint a m
  disjoint a n
  disjoint a o
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint J a
  disjoint b j
  disjoint b m
  disjoint b n
  disjoint b o
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint J b
  disjoint j m
  disjoint j n
  disjoint j o
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint J j
  disjoint m u
  disjoint m v
  disjoint J m
  disjoint n u
  disjoint n v
  disjoint J n
  disjoint o u
  disjoint o v
  disjoint J o
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint J u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint J v
  disjoint J w
  disjoint J z
  disjoint F a
  disjoint F b
  disjoint F m
  disjoint F n
  disjoint F o
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F z
  disjoint ph w
  disjoint ph z
  disjoint X a
  disjoint X b
  disjoint X m
  disjoint X n
  disjoint X o
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X z
  disjoint U w
  disjoint U z
  disjoint V x
  assert |- ( ( J e. ( TopOn ` X ) /\ ( KQ ` J ) e. Nrm ) -> J e. Nrm )

  proof
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cJ
    ckq
    cfv
    #
    cnrm
    wcel
    #
    wa
    #
    cJ
    ctop
    wcel
    #
    vw
    cv
    #
    vu
    cv
    #
    wss
    #
    @7
    cJ
    ccl
    cfv
    #
    cfv
    #
    vz
    cv
    #
    wss
    #
    wa
    #
    vu
    cJ
    wrex
    #
    vw
    cJ
    ccld
    cfv
    #
    @11
    cpw
    #
    cin
    #
    wral
    vz
    cJ
    wral
    cJ
    cnrm
    wcel
    @1
    @5
    @3
    cX
    cJ
    topontop
    adantr
    @4
    @14
    vz
    vw
    cJ
    @17
    @4
    @11
    cJ
    wcel
    #
    @6
    @17
    wcel
    #
    wa
    #
    wa
    #
    cF
    @6
    cima
    #
    vm
    cv
    #
    wss
    #
    @23
    @2
    ccl
    cfv
    cfv
    #
    cF
    @11
    cima
    #
    wss
    #
    wa
    #
    @14
    vm
    @2
    @21
    @3
    @26
    @2
    wcel
    #
    @22
    @2
    ccld
    cfv
    #
    wcel
    #
    @22
    @26
    wss
    #
    @28
    vm
    @2
    wrex
    @1
    @3
    @20
    simplr
    @21
    @1
    @18
    @29
    @1
    @3
    @20
    simpll
    #
    @4
    @18
    @19
    simprl
    #
    vx
    vy
    @11
    cF
    cJ
    cX
    kqval.2
    kqopn
    syl2anc
    @21
    @1
    @6
    @15
    wcel
    #
    @31
    @33
    @21
    @17
    @15
    @6
    @15
    @16
    inss1
    @4
    @18
    @19
    simprr
    #
    sseldi
    #
    vx
    vy
    @6
    cF
    cJ
    cX
    kqval.2
    kqcld
    syl2anc
    @21
    @6
    @16
    wcel
    @6
    @11
    wss
    @32
    @21
    @17
    @16
    @6
    @15
    @16
    inss2
    @36
    sseldi
    @6
    @11
    elpwi
    @6
    @11
    cF
    imass2
    3syl
    vm
    @26
    @22
    @2
    nrmsep3
    syl13anc
    @21
    @23
    @2
    wcel
    #
    @28
    wa
    #
    wa
    #
    cF
    ccnv
    #
    @23
    cima
    #
    cJ
    wcel
    #
    @6
    @42
    wss
    #
    @42
    @9
    cfv
    #
    @11
    wss
    #
    @14
    @40
    cF
    cJ
    @2
    ccn
    co
    wcel
    #
    @38
    @43
    @40
    @1
    @47
    @1
    @3
    @20
    @39
    simplll
    #
    vx
    vy
    cF
    cJ
    cX
    kqval.2
    kqid
    syl
    #
    @21
    @38
    @28
    simprl
    @23
    cF
    cJ
    @2
    cnima
    syl2anc
    @40
    @24
    @44
    @21
    @38
    @24
    @27
    simprrl
    @40
    cF
    wfun
    #
    @6
    cF
    cdm
    #
    wss
    @24
    @44
    wb
    @40
    @1
    cF
    cX
    wfn
    #
    @50
    @48
    vx
    vy
    cF
    cJ
    @0
    cX
    kqval.2
    kqffn
    #
    cX
    cF
    fnfun
    3syl
    @40
    @6
    cJ
    cuni
    #
    @51
    @40
    @35
    @6
    @54
    wss
    @21
    @35
    @39
    @37
    adantr
    @6
    cJ
    @54
    @54
    eqid
    #
    cldss
    syl
    @40
    @51
    cX
    @54
    @40
    @1
    @52
    @51
    cX
    wceq
    @48
    @53
    cX
    cF
    fndm
    3syl
    @40
    @1
    cX
    @54
    wceq
    @48
    cX
    cJ
    toponuni
    syl
    eqtrd
    sseqtr4d
    @6
    @23
    cF
    funimass3
    syl2anc
    mpbid
    @40
    @45
    @41
    @25
    cima
    #
    @11
    @40
    @56
    @15
    wcel
    #
    @42
    @56
    wss
    #
    @45
    @56
    wss
    @40
    @47
    @25
    @30
    wcel
    #
    @57
    @49
    @40
    @2
    ctop
    wcel
    #
    @23
    @2
    cuni
    #
    wss
    #
    @59
    @40
    @1
    @2
    cF
    crn
    #
    ctopon
    cfv
    wcel
    @60
    @48
    vx
    vy
    cF
    cJ
    cX
    kqval.2
    kqtopon
    @63
    @2
    topontop
    3syl
    #
    @38
    @62
    @21
    @28
    @23
    @2
    elssuni
    ad2antrl
    #
    @23
    @2
    @61
    @61
    eqid
    #
    clscld
    syl2anc
    @25
    cF
    cJ
    @2
    cnclima
    syl2anc
    @40
    @23
    @25
    wss
    #
    @58
    @40
    @60
    @62
    @67
    @64
    @65
    @23
    @2
    @61
    @66
    sscls
    syl2anc
    @23
    @25
    @41
    imass2
    syl
    @56
    @42
    cJ
    @54
    @55
    clsss2
    syl2anc
    @40
    @56
    @41
    @26
    cima
    #
    @11
    @40
    @27
    @56
    @68
    wss
    @21
    @38
    @24
    @27
    simprrr
    @25
    @26
    @41
    imass2
    syl
    @40
    @1
    @18
    @68
    @11
    wceq
    @48
    @21
    @18
    @39
    @34
    adantr
    vx
    vy
    @11
    cF
    cJ
    cX
    kqval.2
    kqsat
    syl2anc
    sseqtrd
    sstrd
    @13
    @44
    @46
    wa
    vu
    @42
    cJ
    @7
    @42
    wceq
    #
    @8
    @44
    @12
    @46
    @7
    @42
    @6
    sseq2
    @69
    @10
    @45
    @11
    @7
    @42
    @9
    fveq2
    sseq1d
    anbi12d
    rspcev
    syl12anc
    rexlimddv
    ralrimivva
    vz
    vw
    vu
    cJ
    isnrm
    sylanbrc
end
