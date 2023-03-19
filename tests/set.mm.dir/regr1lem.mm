include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "ccl.mm"
include "cfv.mm"
include "wss.mm"
include "creg.mm"
include "wrex.mm"
include "adantr.mm"
include "simpr.mm"
include "regsep.mm"
include "syl3anc.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "ckq.mm"
include "wn.mm"
include "ad2antrr.mm"
include "cima.mm"
include "cdif.mm"
include "ctopon.mm"
include "ad3antrrr.mm"
include "simplrl.mm"
include "kqopn.mm"
include "syl2anc.mm"
include "cuni.mm"
include "toponuni.mm"
include "syl.mm"
include "difeq1d.mm"
include "ccld.mm"
include "ctop.mm"
include "topontop.mm"
include "elssuni.mm"
include "eqid.mm"
include "clscld.mm"
include "cldopn.mm"
include "eqeltrd.mm"
include "simprrl.mm"
include "wb.mm"
include "kqfvima.mm"
include "mpbid.mm"
include "simprrr.mm"
include "sseld.mm"
include "con3dimp.mm"
include "eldifd.mm"
include "sscls.mm"
include "sscond.mm"
include "imass2.mm"
include "sslin.mm"
include "3syl.mm"
include "kqdisj.mm"
include "sseq0.mm"
include "eleq2.mm"
include "ineq1.mm"
include "eqeq1d.mm"
include "3anbi13d.mm"
include "ineq2.mm"
include "3anbi23d.mm"
include "rspc2ev.mm"
include "syl113anc.mm"
include "ex.mm"
include "mt3d.mm"
include "rexlimddv.mm"

theorem regr1lem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cU: class U
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cJ: class J
  let cX: class X
  let vo: setvar o
  let vw: setvar w
  let vz: setvar z
  let va: setvar a
  let vb: setvar b
  let vj: setvar j
  let vu: setvar u
  let vv: setvar v
  let cV: class V
  assume kqval.2: |- F = ( x e. X |-> { y e. J | x e. y } )
  assume regr1lem.2: |- ( ph -> J e. ( TopOn ` X ) )
  assume regr1lem.3: |- ( ph -> J e. Reg )
  assume regr1lem.4: |- ( ph -> A e. X )
  assume regr1lem.5: |- ( ph -> B e. X )
  assume regr1lem.6: |- ( ph -> U e. J )
  assume regr1lem.7: |- ( ph -> -. E. m e. ( KQ ` J ) E. n e. ( KQ ` J ) ( ( F ` A ) e. m /\ ( F ` B ) e. n /\ ( m i^i n ) = (/) ) )

  disjoint m n
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint J m
  disjoint J n
  disjoint J x
  disjoint J y
  disjoint F m
  disjoint F n
  disjoint X m
  disjoint X n
  disjoint X x
  disjoint X y
  disjoint m o
  disjoint m w
  disjoint m z
  disjoint n o
  disjoint n w
  disjoint n z
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
  disjoint y z
  disjoint A z
  disjoint B w
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
  disjoint n u
  disjoint n v
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
  disjoint F o
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F z
  disjoint ph w
  disjoint ph z
  disjoint X a
  disjoint X b
  disjoint X o
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X z
  disjoint U w
  disjoint U z
  disjoint V x
  assert |- ( ph -> ( A e. U -> B e. U ) )

  proof
    wph
    cA
    cU
    wcel
    #
    cB
    cU
    wcel
    #
    wph
    @0
    wa
    #
    cA
    vz
    cv
    #
    wcel
    #
    @3
    cJ
    ccl
    cfv
    cfv
    #
    cU
    wss
    #
    wa
    #
    @1
    vz
    cJ
    @2
    cJ
    creg
    wcel
    #
    cU
    cJ
    wcel
    #
    @0
    @7
    vz
    cJ
    wrex
    wph
    @8
    @0
    regr1lem.3
    adantr
    wph
    @9
    @0
    regr1lem.6
    adantr
    wph
    @0
    simpr
    vz
    cA
    cU
    cJ
    regsep
    syl3anc
    @2
    @3
    cJ
    wcel
    #
    @7
    wa
    #
    wa
    #
    @1
    cA
    cF
    cfv
    #
    vm
    cv
    #
    wcel
    #
    cB
    cF
    cfv
    #
    vn
    cv
    #
    wcel
    #
    @14
    @17
    cin
    #
    c0
    wceq
    #
    w3a
    #
    vn
    cJ
    ckq
    cfv
    #
    wrex
    vm
    @22
    wrex
    #
    wph
    @23
    wn
    @0
    @11
    regr1lem.7
    ad2antrr
    @12
    @1
    wn
    #
    @23
    @12
    @24
    wa
    #
    cF
    @3
    cima
    #
    @22
    wcel
    #
    cF
    cX
    @5
    cdif
    #
    cima
    #
    @22
    wcel
    #
    @13
    @26
    wcel
    #
    @16
    @29
    wcel
    #
    @26
    @29
    cin
    #
    c0
    wceq
    #
    @23
    @25
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @10
    @27
    wph
    @35
    @0
    @11
    @24
    regr1lem.2
    ad3antrrr
    #
    @2
    @10
    @7
    @24
    simplrl
    #
    vx
    vy
    @3
    cF
    cJ
    cX
    kqval.2
    kqopn
    syl2anc
    @25
    @35
    @28
    cJ
    wcel
    #
    @30
    @36
    @25
    @28
    cJ
    cuni
    #
    @5
    cdif
    #
    cJ
    @25
    cX
    @39
    @5
    @25
    @35
    cX
    @39
    wceq
    @36
    cX
    cJ
    toponuni
    syl
    difeq1d
    @25
    @5
    cJ
    ccld
    cfv
    wcel
    #
    @40
    cJ
    wcel
    @25
    cJ
    ctop
    wcel
    #
    @3
    @39
    wss
    #
    @41
    @25
    @35
    @42
    @36
    cX
    cJ
    topontop
    syl
    #
    @25
    @10
    @43
    @37
    @3
    cJ
    elssuni
    syl
    #
    @3
    cJ
    @39
    @39
    eqid
    #
    clscld
    syl2anc
    @5
    cJ
    @39
    @46
    cldopn
    syl
    eqeltrd
    #
    vx
    vy
    @28
    cF
    cJ
    cX
    kqval.2
    kqopn
    syl2anc
    @25
    @4
    @31
    @12
    @4
    @24
    @2
    @10
    @4
    @6
    simprrl
    adantr
    @25
    @35
    @10
    cA
    cX
    wcel
    #
    @4
    @31
    wb
    @36
    @37
    wph
    @48
    @0
    @11
    @24
    regr1lem.4
    ad3antrrr
    vx
    vy
    cA
    @3
    cF
    cJ
    cX
    kqval.2
    kqfvima
    syl3anc
    mpbid
    @25
    cB
    @28
    wcel
    #
    @32
    @25
    cB
    cX
    @5
    wph
    cB
    cX
    wcel
    #
    @0
    @11
    @24
    regr1lem.5
    ad3antrrr
    #
    @12
    cB
    @5
    wcel
    @1
    @12
    @5
    cU
    cB
    @2
    @10
    @4
    @6
    simprrr
    sseld
    con3dimp
    eldifd
    @25
    @35
    @38
    @50
    @49
    @32
    wb
    @36
    @47
    @51
    vx
    vy
    cB
    @28
    cF
    cJ
    cX
    kqval.2
    kqfvima
    syl3anc
    mpbid
    @25
    @33
    @26
    cF
    cX
    @3
    cdif
    #
    cima
    #
    cin
    #
    wss
    #
    @54
    c0
    wceq
    #
    @34
    @25
    @28
    @52
    wss
    @29
    @53
    wss
    @55
    @25
    @3
    @5
    cX
    @25
    @42
    @43
    @3
    @5
    wss
    @44
    @45
    @3
    cJ
    @39
    @46
    sscls
    syl2anc
    sscond
    @28
    @52
    cF
    imass2
    @29
    @53
    @26
    sslin
    3syl
    @25
    @35
    @10
    @56
    @36
    @37
    vx
    vy
    cX
    @3
    cF
    cJ
    cX
    kqval.2
    kqdisj
    syl2anc
    @33
    @54
    sseq0
    syl2anc
    @21
    @31
    @32
    @34
    w3a
    @31
    @18
    @26
    @17
    cin
    #
    c0
    wceq
    #
    w3a
    vm
    vn
    @26
    @29
    @22
    @22
    @14
    @26
    wceq
    #
    @15
    @31
    @20
    @58
    @18
    @14
    @26
    @13
    eleq2
    @59
    @19
    @57
    c0
    @14
    @26
    @17
    ineq1
    eqeq1d
    3anbi13d
    @17
    @29
    wceq
    #
    @18
    @32
    @58
    @34
    @31
    @17
    @29
    @16
    eleq2
    @60
    @57
    @33
    c0
    @17
    @29
    @26
    ineq2
    eqeq1d
    3anbi23d
    rspc2ev
    syl113anc
    ex
    mt3d
    rexlimddv
    ex
end
