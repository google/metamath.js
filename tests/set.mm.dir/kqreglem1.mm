include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "creg.mm"
include "wa.mm"
include "ckq.mm"
include "ctop.mm"
include "cv.mm"
include "ccl.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "crn.mm"
include "kqtopon.mm"
include "adantr.mm"
include "topontop.mm"
include "syl.mm"
include "wceq.mm"
include "toponss.mm"
include "sylan.mm"
include "sselda.mm"
include "wfn.mm"
include "wb.mm"
include "kqffn.mm"
include "ad3antrrr.mm"
include "fvelrnb.mm"
include "mpbid.mm"
include "wi.mm"
include "ccnv.mm"
include "cima.mm"
include "simpllr.mm"
include "ccn.mm"
include "co.mm"
include "kqid.mm"
include "simplr.mm"
include "cnima.mm"
include "syl2anc.mm"
include "elpreima.mm"
include "biimpar.mm"
include "regsep.mm"
include "syl3anc.mm"
include "simp-4l.mm"
include "simprl.mm"
include "kqopn.mm"
include "simprrl.mm"
include "simplrl.mm"
include "kqfvima.mm"
include "ccld.mm"
include "cuni.mm"
include "elssuni.mm"
include "ad2antrl.mm"
include "eqid.mm"
include "clscld.mm"
include "kqcld.mm"
include "sscls.mm"
include "imass2.mm"
include "clsss2.mm"
include "wfun.mm"
include "fnfun.mm"
include "simprrr.mm"
include "funimass2.mm"
include "sstrd.mm"
include "eleq2.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rexlimddv.mm"
include "expr.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "syl5ibcom.mm"
include "com23.mm"
include "imp.mm"
include "an32s.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "anasss.mm"
include "ralrimivva.mm"
include "isreg.mm"
include "sylanbrc.mm"

theorem kqreglem1
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
  assert |- ( ( J e. ( TopOn ` X ) /\ J e. Reg ) -> ( KQ ` J ) e. Reg )

  proof
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cJ
    creg
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
    vb
    cv
    #
    vm
    cv
    #
    wcel
    #
    @7
    @4
    ccl
    cfv
    #
    cfv
    #
    va
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
    vb
    @11
    wral
    va
    @4
    wral
    @4
    creg
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
    @16
    @2
    vx
    vy
    cF
    cJ
    cX
    kqval.2
    kqtopon
    adantr
    #
    @15
    @4
    topontop
    syl
    @3
    @14
    va
    vb
    @4
    @11
    @3
    @11
    @4
    wcel
    #
    @6
    @11
    wcel
    #
    @14
    @3
    @18
    wa
    #
    @19
    wa
    #
    vz
    cv
    #
    cF
    cfv
    #
    @6
    wceq
    #
    vz
    cX
    wrex
    #
    @14
    @21
    @6
    @15
    wcel
    #
    @25
    @20
    @11
    @15
    @6
    @3
    @16
    @18
    @11
    @15
    wss
    @17
    @11
    @4
    @15
    toponss
    sylan
    sselda
    @21
    cF
    cX
    wfn
    #
    @26
    @25
    wb
    @1
    @27
    @2
    @18
    @19
    vx
    vy
    cF
    cJ
    @0
    cX
    kqval.2
    kqffn
    #
    ad3antrrr
    vz
    cX
    @6
    cF
    fvelrnb
    syl
    mpbid
    @21
    @24
    @14
    vz
    cX
    @20
    @22
    cX
    wcel
    #
    @19
    @24
    @14
    wi
    #
    @20
    @29
    wa
    #
    @19
    @30
    @31
    @24
    @19
    @14
    @31
    @23
    @11
    wcel
    #
    @23
    @7
    wcel
    #
    @12
    wa
    #
    vm
    @4
    wrex
    #
    wi
    @24
    @19
    @14
    wi
    @20
    @29
    @32
    @35
    @20
    @29
    @32
    wa
    #
    wa
    #
    @22
    vw
    cv
    #
    wcel
    #
    @38
    cJ
    ccl
    cfv
    cfv
    #
    cF
    ccnv
    @11
    cima
    #
    wss
    #
    wa
    #
    @35
    vw
    cJ
    @37
    @2
    @41
    cJ
    wcel
    #
    @22
    @41
    wcel
    #
    @43
    vw
    cJ
    wrex
    @1
    @2
    @18
    @36
    simpllr
    @37
    cF
    cJ
    @4
    ccn
    co
    wcel
    #
    @18
    @44
    @1
    @46
    @2
    @18
    @36
    vx
    vy
    cF
    cJ
    cX
    kqval.2
    kqid
    ad3antrrr
    @3
    @18
    @36
    simplr
    @11
    cF
    cJ
    @4
    cnima
    syl2anc
    @20
    @45
    @36
    @20
    @27
    @45
    @36
    wb
    @3
    @27
    @18
    @1
    @27
    @2
    @28
    adantr
    #
    adantr
    cX
    @22
    @11
    cF
    elpreima
    syl
    biimpar
    vw
    @22
    @41
    cJ
    regsep
    syl3anc
    @37
    @38
    cJ
    wcel
    #
    @43
    wa
    #
    wa
    #
    cF
    @38
    cima
    #
    @4
    wcel
    #
    @23
    @51
    wcel
    #
    @51
    @9
    cfv
    #
    @11
    wss
    #
    @35
    @50
    @1
    @48
    @52
    @1
    @2
    @18
    @36
    @49
    simp-4l
    #
    @37
    @48
    @43
    simprl
    #
    vx
    vy
    @38
    cF
    cJ
    cX
    kqval.2
    kqopn
    syl2anc
    @50
    @39
    @53
    @37
    @48
    @39
    @42
    simprrl
    @50
    @1
    @48
    @29
    @39
    @53
    wb
    @56
    @57
    @20
    @29
    @32
    @49
    simplrl
    vx
    vy
    @22
    @38
    cF
    cJ
    cX
    kqval.2
    kqfvima
    syl3anc
    mpbid
    @50
    @54
    cF
    @40
    cima
    #
    @11
    @50
    @58
    @4
    ccld
    cfv
    wcel
    #
    @51
    @58
    wss
    #
    @54
    @58
    wss
    @50
    @1
    @40
    cJ
    ccld
    cfv
    wcel
    #
    @59
    @56
    @50
    cJ
    ctop
    wcel
    #
    @38
    cJ
    cuni
    #
    wss
    #
    @61
    @50
    @1
    @62
    @56
    cX
    cJ
    topontop
    syl
    #
    @48
    @64
    @37
    @43
    @38
    cJ
    elssuni
    ad2antrl
    #
    @38
    cJ
    @63
    @63
    eqid
    #
    clscld
    syl2anc
    vx
    vy
    @40
    cF
    cJ
    cX
    kqval.2
    kqcld
    syl2anc
    @50
    @38
    @40
    wss
    #
    @60
    @50
    @62
    @64
    @68
    @65
    @66
    @38
    cJ
    @63
    @67
    sscls
    syl2anc
    @38
    @40
    cF
    imass2
    syl
    @58
    @51
    @4
    @4
    cuni
    #
    @69
    eqid
    clsss2
    syl2anc
    @50
    cF
    wfun
    #
    @42
    @58
    @11
    wss
    @50
    @27
    @70
    @3
    @27
    @18
    @36
    @49
    @47
    ad3antrrr
    cX
    cF
    fnfun
    syl
    @37
    @48
    @39
    @42
    simprrr
    @40
    @11
    cF
    funimass2
    syl2anc
    sstrd
    @34
    @53
    @55
    wa
    vm
    @51
    @4
    @7
    @51
    wceq
    #
    @33
    @53
    @12
    @55
    @7
    @51
    @23
    eleq2
    @71
    @10
    @54
    @11
    @7
    @51
    @9
    fveq2
    sseq1d
    anbi12d
    rspcev
    syl12anc
    rexlimddv
    expr
    @24
    @32
    @19
    @35
    @14
    @23
    @6
    @11
    eleq1
    @24
    @34
    @13
    vm
    @4
    @24
    @33
    @8
    @12
    @23
    @6
    @7
    eleq1
    anbi1d
    rexbidv
    imbi12d
    syl5ibcom
    com23
    imp
    an32s
    rexlimdva
    mpd
    anasss
    ralrimivva
    va
    vb
    vm
    @4
    isreg
    sylanbrc
end
