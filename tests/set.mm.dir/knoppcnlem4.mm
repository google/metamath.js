include "cfv.mm"
include "cabs.mm"
include "cexp.mm"
include "co.mm"
include "c2.mm"
include "cmul.mm"
include "cn0.mm"
include "cv.mm"
include "cmpt.mm"
include "cle.mm"
include "knoppcnlem1.mm"
include "fveq2d.mm"
include "recnd.mm"
include "expcld.mm"
include "cr.mm"
include "wcel.mm"
include "2re.mm"
include "a1i.mm"
include "cn.mm"
include "nnre.mm"
include "syl.mm"
include "remulcld.mm"
include "reexpcld.mm"
include "dnicld2.mm"
include "absmuld.mm"
include "absexpd.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "c1.mm"
include "abscld.mm"
include "1red.mm"
include "absge0d.mm"
include "expge0d.mm"
include "cdiv.mm"
include "caddc.mm"
include "cfl.mm"
include "cmin.mm"
include "wceq.mm"
include "dnival.mm"
include "cc.mm"
include "halfre.mm"
include "readdcld.mm"
include "reflcl.mm"
include "resubcld.mm"
include "absidm.mm"
include "eqeltrrd.mm"
include "wbr.mm"
include "rddif.mm"
include "clt.mm"
include "halflt1.mm"
include "1re.mm"
include "ltlei.mm"
include "ax-mp.mm"
include "letrd.mm"
include "eqbrtrd.mm"
include "lemul2ad.mm"
include "ax-1rid.mm"
include "breqtrd.mm"
include "eqidd.mm"
include "oveq2.mm"
include "adantl.mm"
include "fvmptd.mm"
include "eqcomd.mm"

theorem knoppcnlem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cC: class C
  let cT: class T
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cN: class N
  assume knoppcnlem4.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppcnlem4.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppcnlem4.n: |- ( ph -> N e. NN )
  assume knoppcnlem4.1: |- ( ph -> C e. RR )
  assume knoppcnlem4.2: |- ( ph -> A e. RR )
  assume knoppcnlem4.3: |- ( ph -> M e. NN0 )

  disjoint A n
  disjoint A y
  disjoint n y
  disjoint A x
  disjoint C m
  disjoint C n
  disjoint C y
  disjoint M m
  disjoint M n
  disjoint M x
  disjoint N n
  disjoint N y
  disjoint N x
  disjoint T n
  disjoint T y
  disjoint m ph
  disjoint n ph
  disjoint ph y
  assert |- ( ph -> ( abs ` ( ( F ` A ) ` M ) ) <_ ( ( m e. NN0 |-> ( ( abs ` C ) ^ m ) ) ` M ) )

  proof
    wph
    cM
    cA
    cF
    cfv
    cfv
    #
    cabs
    cfv
    cC
    cM
    cexp
    co
    #
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
    #
    cmul
    co
    #
    cabs
    cfv
    #
    cM
    vm
    cn0
    cC
    cabs
    cfv
    #
    vm
    cv
    #
    cexp
    co
    #
    cmpt
    #
    cfv
    #
    cle
    wph
    @0
    @6
    cabs
    wph
    vy
    cA
    cC
    cT
    vn
    cF
    cM
    cN
    knoppcnlem4.f
    knoppcnlem4.2
    knoppcnlem4.3
    knoppcnlem1
    fveq2d
    wph
    @7
    @8
    cM
    cexp
    co
    #
    @12
    cle
    wph
    @7
    @13
    @5
    cabs
    cfv
    #
    cmul
    co
    #
    @13
    cle
    wph
    @7
    @1
    cabs
    cfv
    #
    @14
    cmul
    co
    @15
    wph
    @1
    @5
    wph
    cC
    cM
    wph
    cC
    knoppcnlem4.1
    recnd
    #
    knoppcnlem4.3
    expcld
    wph
    @5
    wph
    vx
    @4
    cT
    knoppcnlem4.t
    wph
    @3
    cA
    wph
    @2
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
    knoppcnlem4.n
    cN
    nnre
    syl
    remulcld
    knoppcnlem4.3
    reexpcld
    knoppcnlem4.2
    remulcld
    #
    dnicld2
    #
    recnd
    #
    absmuld
    wph
    @16
    @13
    @14
    cmul
    wph
    cC
    cM
    @17
    knoppcnlem4.3
    absexpd
    oveq1d
    eqtrd
    wph
    @15
    @13
    c1
    cmul
    co
    #
    @13
    cle
    wph
    @14
    c1
    @13
    wph
    @5
    @20
    abscld
    wph
    1red
    #
    wph
    @8
    cM
    wph
    cC
    @17
    abscld
    #
    knoppcnlem4.3
    reexpcld
    #
    wph
    @8
    cM
    @23
    knoppcnlem4.3
    wph
    cC
    @17
    absge0d
    expge0d
    wph
    @14
    @4
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    cfl
    cfv
    #
    @4
    cmin
    co
    #
    cabs
    cfv
    #
    c1
    cle
    wph
    @14
    @29
    cabs
    cfv
    #
    @29
    wph
    @5
    @29
    cabs
    wph
    @4
    cr
    wcel
    #
    @5
    @29
    wceq
    @18
    vx
    @4
    cT
    knoppcnlem4.t
    dnival
    syl
    #
    fveq2d
    wph
    @28
    cc
    wcel
    @30
    @29
    wceq
    wph
    @28
    wph
    @27
    @4
    wph
    @26
    cr
    wcel
    @27
    cr
    wcel
    wph
    @4
    @25
    @18
    @25
    cr
    wcel
    wph
    halfre
    a1i
    #
    readdcld
    @26
    reflcl
    syl
    @18
    resubcld
    recnd
    @28
    absidm
    syl
    eqtrd
    wph
    @29
    @25
    c1
    wph
    @5
    @29
    cr
    @32
    @19
    eqeltrrd
    @33
    @22
    wph
    @31
    @29
    @25
    cle
    wbr
    @18
    @4
    rddif
    syl
    @25
    c1
    cle
    wbr
    #
    wph
    @25
    c1
    clt
    wbr
    @34
    halflt1
    @25
    c1
    halfre
    1re
    ltlei
    ax-mp
    a1i
    letrd
    eqbrtrd
    lemul2ad
    wph
    @13
    cr
    wcel
    @21
    @13
    wceq
    @24
    @13
    ax-1rid
    syl
    breqtrd
    eqbrtrd
    wph
    @12
    @13
    wph
    vm
    cM
    @10
    @13
    cn0
    @11
    cr
    wph
    @11
    eqidd
    @9
    cM
    wceq
    @10
    @13
    wceq
    wph
    @9
    cM
    @8
    cexp
    oveq2
    adantl
    knoppcnlem4.3
    @24
    fvmptd
    eqcomd
    breqtrd
    eqbrtrd
end
