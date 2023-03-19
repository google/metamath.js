include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "c2.mm"
include "cmul.mm"
include "cr.mm"
include "knoppcnlem1.mm"
include "knoppcnlem2.mm"
include "eqeltrd.mm"

theorem knoppcnlem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cC: class C
  let cT: class T
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cN: class N
  assume knoppcnlem3.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppcnlem3.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppcnlem3.n: |- ( ph -> N e. NN )
  assume knoppcnlem3.1: |- ( ph -> C e. RR )
  assume knoppcnlem3.2: |- ( ph -> A e. RR )
  assume knoppcnlem3.3: |- ( ph -> M e. NN0 )

  disjoint A n
  disjoint A y
  disjoint n y
  disjoint A x
  disjoint C n
  disjoint C y
  disjoint M n
  disjoint M x
  disjoint N n
  disjoint N y
  disjoint N x
  disjoint T n
  disjoint T y
  disjoint n ph
  disjoint ph y
  assert |- ( ph -> ( ( F ` A ) ` M ) e. RR )

  proof
    wph
    cM
    cA
    cF
    cfv
    cfv
    cC
    cM
    cexp
    co
    c2
    cN
    cmul
    co
    cM
    cexp
    co
    cA
    cmul
    co
    cT
    cfv
    cmul
    co
    cr
    wph
    vy
    cA
    cC
    cT
    vn
    cF
    cM
    cN
    knoppcnlem3.f
    knoppcnlem3.2
    knoppcnlem3.3
    knoppcnlem1
    wph
    vx
    cA
    cC
    cT
    cM
    cN
    knoppcnlem3.t
    knoppcnlem3.n
    knoppcnlem3.1
    knoppcnlem3.2
    knoppcnlem3.3
    knoppcnlem2
    eqeltrd
end
