include "cpw.mm"
include "wcel.mm"
include "cfi.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "c0.mm"
include "cv.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "cuni.mm"
include "wi.mm"
include "w3a.mm"
include "crab.mm"
include "ssrab2.mm"
include "cint.mm"
include "syl6eleq.mm"
include "sseldi.mm"
include "elpwid.mm"
include "ldsysgenld.mm"
include "syl5eqel.mm"
include "wceq.mm"
include "cin.mm"
include "simprr.mm"
include "simprl.mm"
include "adantr.mm"
include "simpr.mm"
include "sselda.mm"
include "incom.mm"
include "ad2antrr.mm"
include "ldgenpisyslem3.mm"
include "simplr.mm"
include "sseldd.mm"
include "ineq2.mm"
include "eleq1d.mm"
include "elrab.mm"
include "sylib.mm"
include "simprd.mm"
include "syl5eqelr.mm"
include "jca.mm"
include "sylibr.mm"
include "ex.mm"
include "ssrdv.mm"
include "ldgenpisyslem2.mm"
include "syldan.mm"
include "ssrab.mm"
include "rspcv.mm"
include "sylc.mm"
include "ralrimivva.mm"
include "wb.mm"
include "inficl.mm"
include "syl.mm"
include "mpbid.mm"
include "eqimss.mm"
include "ispisys.mm"

theorem ldgenpisys
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cP: class P
  let cT: class T
  let cE: class E
  let cL: class L
  let cO: class O
  let cV: class V
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let vz: setvar z
  let vu: setvar u
  let cS: class S
  assume dynkin.p: |- P = { s e. ~P ~P O | ( fi ` s ) C_ s }
  assume dynkin.l: |- L = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s ( O \ x ) e. s /\ A. x e. ~P s ( ( x ~<_ _om /\ Disj_ y e. x y ) -> U. x e. s ) ) }
  assume dynkin.o: |- ( ph -> O e. V )
  assume ldgenpisys.e: |- E = |^| { t e. L | T C_ t }
  assume ldgenpisys.1: |- ( ph -> T e. P )

  disjoint E s
  disjoint E t
  disjoint E x
  disjoint E y
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint L y
  disjoint O y
  disjoint T y
  disjoint V x
  disjoint ph y
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint L t
  disjoint L x
  disjoint L y
  disjoint O s
  disjoint O t
  disjoint O x
  disjoint P t
  disjoint P x
  disjoint P y
  disjoint L s
  disjoint T s
  disjoint T t
  disjoint T x
  disjoint ph t
  disjoint ph x
  disjoint E a
  disjoint E b
  disjoint E c
  disjoint a b
  disjoint a c
  disjoint a s
  disjoint a t
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b s
  disjoint b t
  disjoint b x
  disjoint b y
  disjoint c s
  disjoint c t
  disjoint c x
  disjoint c y
  disjoint L b
  disjoint O b
  disjoint O c
  disjoint T b
  disjoint T c
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint f i
  disjoint f n
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint i n
  disjoint i s
  disjoint i t
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint n s
  disjoint n t
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint s z
  disjoint t z
  disjoint x z
  disjoint y z
  disjoint L f
  disjoint L i
  disjoint L n
  disjoint P f
  disjoint P i
  disjoint P n
  disjoint L u
  disjoint s u
  disjoint t u
  disjoint u x
  disjoint O u
  disjoint S t
  disjoint T u
  assert |- ( ph -> E e. P )

  proof
    wph
    cE
    cO
    cpw
    #
    cpw
    #
    wcel
    #
    cE
    cfi
    cfv
    #
    cE
    wss
    #
    wa
    cE
    cP
    wcel
    wph
    @2
    @4
    wph
    c0
    vs
    cv
    #
    wcel
    cO
    vx
    cv
    #
    cdif
    @5
    wcel
    vx
    @5
    wral
    @6
    com
    cdom
    wbr
    vy
    @6
    vy
    cv
    wdisj
    wa
    @6
    cuni
    @5
    wcel
    wi
    vx
    @5
    cpw
    wral
    w3a
    #
    vs
    @1
    crab
    #
    @1
    cE
    @7
    vs
    @1
    ssrab2
    wph
    cE
    cL
    @8
    wph
    cE
    cT
    vt
    cv
    wss
    vt
    cL
    crab
    cint
    cL
    ldgenpisys.e
    wph
    vx
    vy
    vt
    cT
    cL
    cO
    cV
    vs
    dynkin.l
    dynkin.o
    wph
    cT
    @0
    wph
    @5
    cfi
    cfv
    @5
    wss
    #
    vs
    @1
    crab
    #
    @1
    cT
    @9
    vs
    @1
    ssrab2
    wph
    cT
    cP
    @10
    ldgenpisys.1
    dynkin.p
    syl6eleq
    sseldi
    elpwid
    #
    ldsysgenld
    syl5eqel
    #
    dynkin.l
    syl6eleq
    sseldi
    wph
    @3
    cE
    wceq
    #
    @4
    wph
    va
    cv
    #
    vb
    cv
    #
    cin
    #
    cE
    wcel
    #
    vb
    cE
    wral
    va
    cE
    wral
    #
    @13
    wph
    @17
    va
    vb
    cE
    cE
    wph
    @14
    cE
    wcel
    #
    @15
    cE
    wcel
    #
    wa
    #
    wa
    #
    @20
    @14
    vc
    cv
    #
    cin
    #
    cE
    wcel
    #
    vc
    cE
    wral
    #
    @17
    wph
    @19
    @20
    simprr
    @22
    cE
    @0
    wss
    #
    @26
    @22
    cE
    @25
    vc
    @0
    crab
    #
    wss
    #
    @27
    @26
    wa
    wph
    @21
    @19
    @29
    wph
    @19
    @20
    simprl
    wph
    @19
    wa
    #
    vx
    vy
    vt
    @14
    cP
    cT
    cE
    cL
    cO
    cV
    vs
    vc
    dynkin.p
    dynkin.l
    wph
    cO
    cV
    wcel
    #
    @19
    dynkin.o
    adantr
    ldgenpisys.e
    wph
    cT
    cP
    wcel
    #
    @19
    ldgenpisys.1
    adantr
    wph
    @19
    simpr
    @30
    vb
    cT
    @28
    @30
    @15
    cT
    wcel
    #
    @15
    @28
    wcel
    #
    @30
    @33
    wa
    #
    @15
    @0
    wcel
    #
    @17
    wa
    @34
    @35
    @36
    @17
    @30
    cT
    @0
    @15
    wph
    cT
    @0
    wss
    @19
    @11
    adantr
    sselda
    @35
    @16
    @15
    @14
    cin
    #
    cE
    @15
    @14
    incom
    @35
    @14
    @0
    wcel
    #
    @37
    cE
    wcel
    #
    @35
    @14
    @15
    @23
    cin
    #
    cE
    wcel
    #
    vc
    @0
    crab
    #
    wcel
    @38
    @39
    wa
    @35
    cE
    @42
    @14
    @35
    vx
    vy
    vt
    @15
    cP
    cT
    cE
    cL
    cO
    cV
    vs
    vc
    dynkin.p
    dynkin.l
    wph
    @31
    @19
    @33
    dynkin.o
    ad2antrr
    ldgenpisys.e
    wph
    @32
    @19
    @33
    ldgenpisys.1
    ad2antrr
    @30
    @33
    simpr
    ldgenpisyslem3
    wph
    @19
    @33
    simplr
    sseldd
    @41
    @39
    vc
    @14
    @0
    @23
    @14
    wceq
    @40
    @37
    cE
    @23
    @14
    @15
    ineq2
    eleq1d
    elrab
    sylib
    simprd
    syl5eqelr
    jca
    @25
    @17
    vc
    @15
    @0
    @23
    @15
    wceq
    @24
    @16
    cE
    @23
    @15
    @14
    ineq2
    eleq1d
    #
    elrab
    sylibr
    ex
    ssrdv
    ldgenpisyslem2
    syldan
    @25
    vc
    @0
    cE
    ssrab
    sylib
    simprd
    @25
    @17
    vc
    @15
    cE
    @43
    rspcv
    sylc
    ralrimivva
    wph
    cE
    cL
    wcel
    @18
    @13
    wb
    @12
    va
    vb
    cE
    cL
    inficl
    syl
    mpbid
    @3
    cE
    eqimss
    syl
    jca
    cP
    cE
    cO
    vs
    dynkin.p
    ispisys
    sylibr
end
