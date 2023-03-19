include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "cin.mm"
include "crest.mm"
include "co.mm"
include "smflimlem2.mm"
include "smflimlem4.mm"
include "eqssd.mm"
include "smflimlem1.mm"
include "eqeltrd.mm"

theorem smflimlem5
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cS: class S
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cM: class M
  let cZ: class Z
  let vs: setvar s
  let vr: setvar r
  assume smflimlem5.1: |- ( ph -> M e. ZZ )
  assume smflimlem5.2: |- Z = ( ZZ>= ` M )
  assume smflimlem5.3: |- ( ph -> S e. SAlg )
  assume smflimlem5.4: |- ( ph -> F : Z --> ( SMblFn ` S ) )
  assume smflimlem5.5: |- D = { x e. U_ n e. Z |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) | ( m e. Z |-> ( ( F ` m ) ` x ) ) e. dom ~~> }
  assume smflimlem5.6: |- G = ( x e. D |-> ( ~~> ` ( m e. Z |-> ( ( F ` m ) ` x ) ) ) )
  assume smflimlem5.7: |- ( ph -> A e. RR )
  assume smflimlem5.8: |- P = ( m e. Z , k e. NN |-> { s e. S | { x e. dom ( F ` m ) | ( ( F ` m ) ` x ) < ( A + ( 1 / k ) ) } = ( s i^i dom ( F ` m ) ) } )
  assume smflimlem5.9: |- H = ( m e. Z , k e. NN |-> ( C ` ( m P k ) ) )
  assume smflimlem5.10: |- I = |^|_ k e. NN U_ n e. Z |^|_ m e. ( ZZ>= ` n ) ( m H k )
  assume smflimlem5.11: |- ( ( ph /\ r e. ran P ) -> ( C ` r ) e. r )

  disjoint A k
  disjoint A m
  disjoint A n
  disjoint A x
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint m n
  disjoint m x
  disjoint n x
  disjoint A s
  disjoint k s
  disjoint m s
  disjoint s x
  disjoint C k
  disjoint C m
  disjoint C r
  disjoint k r
  disjoint m r
  disjoint C s
  disjoint D k
  disjoint D m
  disjoint D n
  disjoint D x
  disjoint D r
  disjoint r x
  disjoint F k
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint F s
  disjoint G k
  disjoint G m
  disjoint G n
  disjoint H k
  disjoint H m
  disjoint H n
  disjoint H s
  disjoint I k
  disjoint I m
  disjoint I r
  disjoint I x
  disjoint M m
  disjoint P k
  disjoint P m
  disjoint P r
  disjoint P s
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S s
  disjoint Z k
  disjoint Z m
  disjoint Z n
  disjoint Z x
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint ph r
  disjoint k x
  assert |- ( ph -> { x e. D | ( G ` x ) <_ A } e. ( S |`t D ) )

  proof
    wph
    vx
    cv
    cG
    cfv
    cA
    cle
    wbr
    vx
    cD
    crab
    #
    cD
    cI
    cin
    #
    cS
    cD
    crest
    co
    wph
    @0
    @1
    wph
    vx
    cA
    cC
    cD
    cP
    cS
    vk
    vm
    vn
    cF
    cG
    cH
    cI
    cM
    cZ
    vs
    vr
    smflimlem5.2
    smflimlem5.3
    smflimlem5.4
    smflimlem5.5
    smflimlem5.6
    smflimlem5.7
    smflimlem5.8
    smflimlem5.9
    smflimlem5.10
    smflimlem5.11
    smflimlem2
    wph
    vx
    cA
    cC
    cD
    cP
    cS
    vk
    vm
    vn
    cF
    cG
    cH
    cI
    cM
    cZ
    vs
    vr
    smflimlem5.1
    smflimlem5.2
    smflimlem5.3
    smflimlem5.4
    smflimlem5.5
    smflimlem5.6
    smflimlem5.7
    smflimlem5.8
    smflimlem5.9
    smflimlem5.10
    smflimlem5.11
    smflimlem4
    eqssd
    wph
    vx
    cA
    cC
    cD
    cP
    cS
    vk
    vm
    vn
    cF
    cH
    cI
    cM
    cZ
    vs
    vr
    smflimlem5.2
    smflimlem5.3
    smflimlem5.5
    smflimlem5.8
    smflimlem5.9
    smflimlem5.10
    smflimlem5.11
    smflimlem1
    eqeltrd
end
