include "cv.mm"
include "wss.mm"
include "crab.mm"
include "cint.mm"
include "wi.mm"
include "wral.mm"
include "id.mm"
include "rgenw.mm"
include "ssintrab.mm"
include "mpbir.mm"
include "sseqtr4i.mm"
include "sseldi.mm"
include "cpw.mm"
include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "cfi.mm"
include "cfv.mm"
include "ispisys.mm"
include "sylib.mm"
include "simpld.mm"
include "elpwi.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "inelpisys.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "jca.mm"
include "ssrab.mm"
include "sylibr.mm"
include "ldgenpisyslem2.mm"

theorem ldgenpisyslem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cA: class A
  let cP: class P
  let cT: class T
  let cE: class E
  let cL: class L
  let cO: class O
  let cV: class V
  let vs: setvar s
  let vb: setvar b
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
  assume ldgenpisyslem3.1: |- ( ph -> A e. T )

  disjoint A b
  disjoint A s
  disjoint A t
  disjoint A x
  disjoint A y
  disjoint b s
  disjoint b t
  disjoint b x
  disjoint b y
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint E b
  disjoint E s
  disjoint E t
  disjoint E x
  disjoint E y
  disjoint L y
  disjoint O b
  disjoint O y
  disjoint T b
  disjoint T s
  disjoint T t
  disjoint T x
  disjoint T y
  disjoint V x
  disjoint b ph
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
  assert |- ( ph -> E C_ { b e. ~P O | ( A i^i b ) e. E } )

  proof
    wph
    vx
    vy
    vt
    cA
    cP
    cT
    cE
    cL
    cO
    cV
    vs
    vb
    dynkin.p
    dynkin.l
    dynkin.o
    ldgenpisys.e
    ldgenpisys.1
    wph
    cT
    cE
    cA
    cT
    cT
    vt
    cv
    wss
    #
    vt
    cL
    crab
    cint
    #
    cE
    cT
    @1
    wss
    @0
    @0
    wi
    #
    vt
    cL
    wral
    @2
    vt
    cL
    @0
    id
    rgenw
    @0
    vt
    cT
    cL
    ssintrab
    mpbir
    ldgenpisys.e
    sseqtr4i
    #
    ldgenpisyslem3.1
    sseldi
    wph
    cT
    cO
    cpw
    #
    wss
    #
    cA
    vb
    cv
    #
    cin
    #
    cE
    wcel
    #
    vb
    cT
    wral
    #
    wa
    cT
    @8
    vb
    @4
    crab
    wss
    wph
    @5
    @9
    wph
    cT
    @4
    cpw
    wcel
    #
    @5
    wph
    @10
    cT
    cfi
    cfv
    cT
    wss
    #
    wph
    cT
    cP
    wcel
    #
    @10
    @11
    wa
    ldgenpisys.1
    cP
    cT
    cO
    vs
    dynkin.p
    ispisys
    sylib
    simpld
    cT
    @4
    elpwi
    syl
    wph
    @8
    vb
    cT
    wph
    @6
    cT
    wcel
    #
    wa
    #
    cT
    cE
    @7
    @3
    @14
    @12
    cA
    cT
    wcel
    #
    @13
    @7
    cT
    wcel
    wph
    @12
    @13
    ldgenpisys.1
    adantr
    wph
    @15
    @13
    ldgenpisyslem3.1
    adantr
    wph
    @13
    simpr
    cA
    @6
    cP
    cT
    cO
    vs
    dynkin.p
    inelpisys
    syl3anc
    sseldi
    ralrimiva
    jca
    @8
    vb
    @4
    cT
    ssrab
    sylibr
    ldgenpisyslem2
end
