include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ckq.mm"
include "creg.mm"
include "wa.mm"
include "ctop.mm"
include "cv.mm"
include "ccl.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "topontop.mm"
include "adantr.mm"
include "cima.mm"
include "simplr.mm"
include "simpll.mm"
include "simprl.mm"
include "kqopn.mm"
include "syl2anc.mm"
include "simprr.mm"
include "wb.mm"
include "toponss.mm"
include "sseldd.mm"
include "kqfvima.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "regsep.mm"
include "ccnv.mm"
include "ccn.mm"
include "co.mm"
include "kqid.mm"
include "syl.mm"
include "cnima.mm"
include "simprrl.mm"
include "wfn.mm"
include "kqffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "mpbir2and.mm"
include "ccld.mm"
include "cuni.mm"
include "crn.mm"
include "kqtopon.mm"
include "elssuni.mm"
include "ad2antrl.mm"
include "eqid.mm"
include "clscld.mm"
include "cnclima.mm"
include "sscls.mm"
include "imass2.mm"
include "clsss2.mm"
include "simprrr.mm"
include "wceq.mm"
include "kqsat.mm"
include "sseqtrd.mm"
include "sstrd.mm"
include "eleq2.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rexlimddv.mm"
include "ralrimivva.mm"
include "isreg.mm"
include "sylanbrc.mm"

theorem kqreglem2
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
  assert |- ( ( J e. ( TopOn ` X ) /\ ( KQ ` J ) e. Reg ) -> J e. Reg )

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
    creg
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
    vm
    cv
    #
    wcel
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
    vm
    cJ
    wrex
    #
    vw
    @11
    wral
    vz
    cJ
    wral
    cJ
    creg
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
    @11
    @4
    @11
    cJ
    wcel
    #
    @6
    @11
    wcel
    #
    wa
    #
    wa
    #
    @6
    cF
    cfv
    #
    vn
    cv
    #
    wcel
    #
    @20
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
    vn
    @2
    @18
    @3
    @23
    @2
    wcel
    #
    @19
    @23
    wcel
    #
    @25
    vn
    @2
    wrex
    @1
    @3
    @17
    simplr
    @18
    @1
    @15
    @26
    @1
    @3
    @17
    simpll
    #
    @4
    @15
    @16
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
    @18
    @16
    @27
    @4
    @15
    @16
    simprr
    #
    @18
    @1
    @15
    @6
    cX
    wcel
    #
    @16
    @27
    wb
    @28
    @29
    @18
    @11
    cX
    @6
    @18
    @1
    @15
    @11
    cX
    wss
    @28
    @29
    @11
    cJ
    cX
    toponss
    syl2anc
    @30
    sseldd
    #
    vx
    vy
    @6
    @11
    cF
    cJ
    cX
    kqval.2
    kqfvima
    syl3anc
    mpbid
    vn
    @19
    @23
    @2
    regsep
    syl3anc
    @18
    @20
    @2
    wcel
    #
    @25
    wa
    #
    wa
    #
    cF
    ccnv
    #
    @20
    cima
    #
    cJ
    wcel
    #
    @6
    @37
    wcel
    #
    @37
    @9
    cfv
    #
    @11
    wss
    #
    @14
    @35
    cF
    cJ
    @2
    ccn
    co
    wcel
    #
    @33
    @38
    @35
    @1
    @42
    @18
    @1
    @34
    @28
    adantr
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
    @18
    @33
    @25
    simprl
    @20
    cF
    cJ
    @2
    cnima
    syl2anc
    @35
    @39
    @31
    @21
    @18
    @31
    @34
    @32
    adantr
    @18
    @33
    @21
    @24
    simprrl
    @35
    @1
    cF
    cX
    wfn
    @39
    @31
    @21
    wa
    wb
    @43
    vx
    vy
    cF
    cJ
    @0
    cX
    kqval.2
    kqffn
    cX
    @6
    @20
    cF
    elpreima
    3syl
    mpbir2and
    @35
    @40
    @36
    @22
    cima
    #
    @11
    @35
    @45
    cJ
    ccld
    cfv
    wcel
    #
    @37
    @45
    wss
    #
    @40
    @45
    wss
    @35
    @42
    @22
    @2
    ccld
    cfv
    wcel
    #
    @46
    @44
    @35
    @2
    ctop
    wcel
    #
    @20
    @2
    cuni
    #
    wss
    #
    @48
    @35
    @1
    @2
    cF
    crn
    #
    ctopon
    cfv
    wcel
    @49
    @43
    vx
    vy
    cF
    cJ
    cX
    kqval.2
    kqtopon
    @52
    @2
    topontop
    3syl
    #
    @33
    @51
    @18
    @25
    @20
    @2
    elssuni
    ad2antrl
    #
    @20
    @2
    @50
    @50
    eqid
    #
    clscld
    syl2anc
    @22
    cF
    cJ
    @2
    cnclima
    syl2anc
    @35
    @20
    @22
    wss
    #
    @47
    @35
    @49
    @51
    @56
    @53
    @54
    @20
    @2
    @50
    @55
    sscls
    syl2anc
    @20
    @22
    @36
    imass2
    syl
    @45
    @37
    cJ
    cJ
    cuni
    #
    @57
    eqid
    clsss2
    syl2anc
    @35
    @45
    @36
    @23
    cima
    #
    @11
    @35
    @24
    @45
    @58
    wss
    @18
    @33
    @21
    @24
    simprrr
    @22
    @23
    @36
    imass2
    syl
    @35
    @1
    @15
    @58
    @11
    wceq
    @43
    @18
    @15
    @34
    @29
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
    @39
    @41
    wa
    vm
    @37
    cJ
    @7
    @37
    wceq
    #
    @8
    @39
    @12
    @41
    @7
    @37
    @6
    eleq2
    @59
    @10
    @40
    @11
    @7
    @37
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
    cJ
    isreg
    sylanbrc
end
