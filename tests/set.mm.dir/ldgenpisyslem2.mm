include "cv.mm"
include "wss.mm"
include "crab.mm"
include "cint.mm"
include "cin.mm"
include "wcel.mm"
include "cpw.mm"
include "wa.mm"
include "ldgenpisyslem1.mm"
include "jca.mm"
include "sseq2.mm"
include "elrab.mm"
include "sylibr.mm"
include "intss1.mm"
include "syl.mm"
include "syl5eqss.mm"

theorem ldgenpisyslem2
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
  let vz: setvar z
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let vu: setvar u
  let cS: class S
  assume dynkin.p: |- P = { s e. ~P ~P O | ( fi ` s ) C_ s }
  assume dynkin.l: |- L = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s ( O \ x ) e. s /\ A. x e. ~P s ( ( x ~<_ _om /\ Disj_ y e. x y ) -> U. x e. s ) ) }
  assume dynkin.o: |- ( ph -> O e. V )
  assume ldgenpisys.e: |- E = |^| { t e. L | T C_ t }
  assume ldgenpisys.1: |- ( ph -> T e. P )
  assume ldgenpisyslem1.1: |- ( ph -> A e. E )
  assume ldgenpisyslem2.1: |- ( ph -> T C_ { b e. ~P O | ( A i^i b ) e. E } )

  disjoint b s
  disjoint b x
  disjoint s x
  disjoint A b
  disjoint A s
  disjoint A t
  disjoint A x
  disjoint A y
  disjoint b t
  disjoint b y
  disjoint s t
  disjoint s y
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint E b
  disjoint E s
  disjoint E t
  disjoint E x
  disjoint E y
  disjoint O b
  disjoint O t
  disjoint O y
  disjoint V x
  disjoint T y
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
  disjoint A z
  disjoint b z
  disjoint s z
  disjoint t z
  disjoint x z
  disjoint y z
  disjoint L z
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
    cE
    cT
    vt
    cv
    #
    wss
    #
    vt
    cL
    crab
    #
    cint
    #
    cA
    vb
    cv
    cin
    cE
    wcel
    vb
    cO
    cpw
    crab
    #
    ldgenpisys.e
    wph
    @4
    @2
    wcel
    #
    @3
    @4
    wss
    wph
    @4
    cL
    wcel
    #
    cT
    @4
    wss
    #
    wa
    @5
    wph
    @6
    @7
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
    ldgenpisyslem1.1
    ldgenpisyslem1
    ldgenpisyslem2.1
    jca
    @1
    @7
    vt
    @4
    cL
    @0
    @4
    cT
    sseq2
    elrab
    sylibr
    @4
    @2
    intss1
    syl
    syl5eqss
end
