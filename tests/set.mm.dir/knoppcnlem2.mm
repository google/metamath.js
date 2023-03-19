include "cexp.mm"
include "co.mm"
include "c2.mm"
include "cmul.mm"
include "cfv.mm"
include "reexpcld.mm"
include "cr.mm"
include "wcel.mm"
include "2re.mm"
include "a1i.mm"
include "cn.mm"
include "nnre.mm"
include "syl.mm"
include "remulcld.mm"
include "dnicld2.mm"

theorem knoppcnlem2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cT: class T
  let cM: class M
  let cN: class N
  assume knoppcnlem2.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppcnlem2.n: |- ( ph -> N e. NN )
  assume knoppcnlem2.1: |- ( ph -> C e. RR )
  assume knoppcnlem2.2: |- ( ph -> A e. RR )
  assume knoppcnlem2.3: |- ( ph -> M e. NN0 )

  disjoint A x
  disjoint M x
  disjoint N x
  assert |- ( ph -> ( ( C ^ M ) x. ( T ` ( ( ( 2 x. N ) ^ M ) x. A ) ) ) e. RR )

  proof
    wph
    cC
    cM
    cexp
    co
    c2
    cN
    cmul
    co
    #
    cM
    cexp
    co
    #
    cA
    cmul
    co
    #
    cT
    cfv
    wph
    cC
    cM
    knoppcnlem2.1
    knoppcnlem2.3
    reexpcld
    wph
    vx
    @2
    cT
    knoppcnlem2.t
    wph
    @1
    cA
    wph
    @0
    cM
    wph
    c2
    cN
    c2
    cr
    wcel
    wph
    2re
    a1i
    wph
    cN
    cn
    wcel
    cN
    cr
    wcel
    knoppcnlem2.n
    cN
    nnre
    syl
    remulcld
    knoppcnlem2.3
    reexpcld
    knoppcnlem2.2
    remulcld
    dnicld2
    remulcld
end
