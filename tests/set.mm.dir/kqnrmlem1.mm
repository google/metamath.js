include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cnrm.mm"
include "wa.mm"
include "ckq.mm"
include "ctop.mm"
include "cv.mm"
include "wss.mm"
include "ccl.mm"
include "wrex.mm"
include "ccld.mm"
include "cpw.mm"
include "cin.mm"
include "wral.mm"
include "crn.mm"
include "kqtopon.mm"
include "adantr.mm"
include "topontop.mm"
include "syl.mm"
include "ccnv.mm"
include "cima.mm"
include "simplr.mm"
include "ccn.mm"
include "co.mm"
include "kqid.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "cnima.mm"
include "syl2anc.mm"
include "inss1.mm"
include "simprr.mm"
include "sseldi.mm"
include "cnclima.mm"
include "inss2.mm"
include "elpwi.mm"
include "imass2.mm"
include "3syl.mm"
include "nrmsep3.mm"
include "syl13anc.mm"
include "simplll.mm"
include "kqopn.mm"
include "simprrl.mm"
include "wfun.mm"
include "wi.mm"
include "wfn.mm"
include "kqffn.mm"
include "fnfun.mm"
include "cuni.mm"
include "eqid.mm"
include "cldss.mm"
include "wceq.mm"
include "toponuni.mm"
include "sseqtr4d.mm"
include "funimass1.mm"
include "mpd.mm"
include "elssuni.mm"
include "ad2antrl.mm"
include "clscld.mm"
include "kqcld.mm"
include "sscls.mm"
include "clsss2.mm"
include "simprrr.mm"
include "cdm.mm"
include "wb.mm"
include "clsss3.mm"
include "fndm.mm"
include "eqtrd.mm"
include "funimass3.mm"
include "mpbird.mm"
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

theorem kqnrmlem1
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
  assert |- ( ( J e. ( TopOn ` X ) /\ J e. Nrm ) -> ( KQ ` J ) e. Nrm )

  proof
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cJ
    cnrm
    wcel
    #
    wa
    #
    cJ
    ckq
    cfv
    #
    ctop
    wcel
    #
    vw
    cv
    #
    vm
    cv
    #
    wss
    #
    @7
    @4
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
    vm
    @4
    wrex
    #
    vw
    @4
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
    @4
    wral
    @4
    cnrm
    wcel
    @3
    @4
    cF
    crn
    #
    ctopon
    cfv
    wcel
    #
    @5
    @1
    @19
    @2
    vx
    vy
    cF
    cJ
    cX
    kqval.2
    kqtopon
    #
    adantr
    @18
    @4
    topontop
    syl
    @3
    @14
    vz
    vw
    @4
    @17
    @3
    @11
    @4
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
    ccnv
    #
    @6
    cima
    #
    vu
    cv
    #
    wss
    #
    @27
    cJ
    ccl
    cfv
    cfv
    #
    @25
    @11
    cima
    #
    wss
    #
    wa
    #
    @14
    vu
    cJ
    @24
    @2
    @30
    cJ
    wcel
    #
    @26
    cJ
    ccld
    cfv
    #
    wcel
    #
    @26
    @30
    wss
    #
    @32
    vu
    cJ
    wrex
    @1
    @2
    @23
    simplr
    @24
    cF
    cJ
    @4
    ccn
    co
    wcel
    #
    @21
    @33
    @1
    @37
    @2
    @23
    vx
    vy
    cF
    cJ
    cX
    kqval.2
    kqid
    ad2antrr
    #
    @3
    @21
    @22
    simprl
    @11
    cF
    cJ
    @4
    cnima
    syl2anc
    @24
    @37
    @6
    @15
    wcel
    #
    @35
    @38
    @24
    @17
    @15
    @6
    @15
    @16
    inss1
    @3
    @21
    @22
    simprr
    #
    sseldi
    #
    @6
    cF
    cJ
    @4
    cnclima
    syl2anc
    @24
    @6
    @16
    wcel
    @6
    @11
    wss
    @36
    @24
    @17
    @16
    @6
    @15
    @16
    inss2
    @40
    sseldi
    @6
    @11
    elpwi
    @6
    @11
    @25
    imass2
    3syl
    vu
    @30
    @26
    cJ
    nrmsep3
    syl13anc
    @24
    @27
    cJ
    wcel
    #
    @32
    wa
    #
    wa
    #
    cF
    @27
    cima
    #
    @4
    wcel
    #
    @6
    @45
    wss
    #
    @45
    @9
    cfv
    #
    @11
    wss
    #
    @14
    @44
    @1
    @42
    @46
    @1
    @2
    @23
    @43
    simplll
    #
    @24
    @42
    @32
    simprl
    vx
    vy
    @27
    cF
    cJ
    cX
    kqval.2
    kqopn
    syl2anc
    @44
    @28
    @47
    @24
    @42
    @28
    @31
    simprrl
    @44
    cF
    wfun
    #
    @6
    @18
    wss
    @28
    @47
    wi
    @44
    @1
    cF
    cX
    wfn
    #
    @51
    @50
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
    #
    @44
    @6
    @4
    cuni
    #
    @18
    @44
    @39
    @6
    @55
    wss
    @24
    @39
    @43
    @41
    adantr
    @6
    @4
    @55
    @55
    eqid
    #
    cldss
    syl
    @44
    @1
    @19
    @18
    @55
    wceq
    @50
    @20
    @18
    @4
    toponuni
    3syl
    sseqtr4d
    @6
    @27
    cF
    funimass1
    syl2anc
    mpd
    @44
    @48
    cF
    @29
    cima
    #
    @11
    @44
    @57
    @15
    wcel
    #
    @45
    @57
    wss
    #
    @48
    @57
    wss
    @44
    @1
    @29
    @34
    wcel
    #
    @58
    @50
    @44
    cJ
    ctop
    wcel
    #
    @27
    cJ
    cuni
    #
    wss
    #
    @60
    @44
    @1
    @61
    @50
    cX
    cJ
    topontop
    syl
    #
    @42
    @63
    @24
    @32
    @27
    cJ
    elssuni
    ad2antrl
    #
    @27
    cJ
    @62
    @62
    eqid
    #
    clscld
    syl2anc
    vx
    vy
    @29
    cF
    cJ
    cX
    kqval.2
    kqcld
    syl2anc
    @44
    @27
    @29
    wss
    #
    @59
    @44
    @61
    @63
    @67
    @64
    @65
    @27
    cJ
    @62
    @66
    sscls
    syl2anc
    @27
    @29
    cF
    imass2
    syl
    @57
    @45
    @4
    @55
    @56
    clsss2
    syl2anc
    @44
    @57
    @11
    wss
    #
    @31
    @24
    @42
    @28
    @31
    simprrr
    @44
    @51
    @29
    cF
    cdm
    #
    wss
    @68
    @31
    wb
    @54
    @44
    @29
    @62
    @69
    @44
    @61
    @63
    @29
    @62
    wss
    @64
    @65
    @27
    cJ
    @62
    @66
    clsss3
    syl2anc
    @44
    @69
    cX
    @62
    @44
    @1
    @52
    @69
    cX
    wceq
    @50
    @53
    cX
    cF
    fndm
    3syl
    @44
    @1
    cX
    @62
    wceq
    @50
    cX
    cJ
    toponuni
    syl
    eqtrd
    sseqtr4d
    @29
    @11
    cF
    funimass3
    syl2anc
    mpbird
    sstrd
    @13
    @47
    @49
    wa
    vm
    @45
    @4
    @7
    @45
    wceq
    #
    @8
    @47
    @12
    @49
    @7
    @45
    @6
    sseq2
    @70
    @10
    @48
    @11
    @7
    @45
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
    vm
    @4
    isnrm
    sylanbrc
end
