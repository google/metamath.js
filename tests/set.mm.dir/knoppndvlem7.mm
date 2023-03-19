include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "c2.mm"
include "cmul.mm"
include "cdiv.mm"
include "cneg.mm"
include "cr.mm"
include "wceq.mm"
include "a1i.mm"
include "nn0zd.mm"
include "knoppndvlem1.mm"
include "eqeltrd.mm"
include "knoppcnlem1.mm"
include "oveq2i.mm"
include "c1.mm"
include "2cnd.mm"
include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "nnz.mm"
include "syl.mm"
include "zcnd.mm"
include "mulcld.mm"
include "expcld.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "0red.mm"
include "1red.mm"
include "zred.mm"
include "clt.mm"
include "wbr.mm"
include "0lt1.mm"
include "cle.mm"
include "nnge1.mm"
include "ltletrd.mm"
include "ltned.mm"
include "necomd.mm"
include "mulne0d.mm"
include "znegcld.mm"
include "expclzd.mm"
include "divcld.mm"
include "mulassd.mm"
include "eqcomd.mm"
include "divassd.mm"
include "expnegd.mm"
include "oveq2d.mm"
include "expne0d.mm"
include "recidd.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "divrec2d.mm"
include "3eqtrd.mm"
include "fveq2d.mm"

theorem knoppndvlem7
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cC: class C
  let cT: class T
  let vn: setvar n
  let cF: class F
  let cJ: class J
  let cM: class M
  let cN: class N
  assume knoppndvlem7.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppndvlem7.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppndvlem7.a: |- A = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. M )
  assume knoppndvlem7.j: |- ( ph -> J e. NN0 )
  assume knoppndvlem7.m: |- ( ph -> M e. ZZ )
  assume knoppndvlem7.n: |- ( ph -> N e. NN )

  disjoint A n
  disjoint A y
  disjoint n y
  disjoint C n
  disjoint C y
  disjoint J n
  disjoint N n
  disjoint N y
  disjoint T n
  disjoint T y
  disjoint n ph
  disjoint ph y
  assert |- ( ph -> ( ( F ` A ) ` J ) = ( ( C ^ J ) x. ( T ` ( M / 2 ) ) ) )

  proof
    wph
    cJ
    cA
    cF
    cfv
    cfv
    cC
    cJ
    cexp
    co
    #
    c2
    cN
    cmul
    co
    #
    cJ
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
    @0
    cM
    c2
    cdiv
    co
    #
    cT
    cfv
    #
    cmul
    co
    wph
    vy
    cA
    cC
    cT
    vn
    cF
    cJ
    cN
    knoppndvlem7.f
    wph
    cA
    @1
    cJ
    cneg
    #
    cexp
    co
    #
    c2
    cdiv
    co
    #
    cM
    cmul
    co
    #
    cr
    cA
    @10
    wceq
    wph
    knoppndvlem7.a
    a1i
    wph
    cJ
    cM
    cN
    knoppndvlem7.n
    wph
    cJ
    knoppndvlem7.j
    nn0zd
    #
    knoppndvlem7.m
    knoppndvlem1
    eqeltrd
    knoppndvlem7.j
    knoppcnlem1
    wph
    @4
    @6
    @0
    cmul
    wph
    @3
    @5
    cT
    wph
    @3
    @2
    @10
    cmul
    co
    #
    @5
    @3
    @12
    wceq
    wph
    cA
    @10
    @2
    cmul
    knoppndvlem7.a
    oveq2i
    a1i
    wph
    @12
    @2
    @9
    cmul
    co
    #
    cM
    cmul
    co
    #
    c1
    c2
    cdiv
    co
    #
    cM
    cmul
    co
    #
    @5
    wph
    @14
    @12
    wph
    @2
    @9
    cM
    wph
    @1
    cJ
    wph
    c2
    cN
    wph
    2cnd
    #
    wph
    cN
    wph
    cN
    cn
    wcel
    #
    cN
    cz
    wcel
    knoppndvlem7.n
    cN
    nnz
    syl
    #
    zcnd
    #
    mulcld
    #
    knoppndvlem7.j
    expcld
    #
    wph
    @8
    c2
    wph
    @1
    @7
    @21
    wph
    c2
    cN
    @17
    @20
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    #
    wph
    cc0
    cN
    wph
    cc0
    cN
    wph
    0red
    #
    wph
    cc0
    c1
    cN
    @24
    wph
    1red
    wph
    cN
    @19
    zred
    cc0
    c1
    clt
    wbr
    wph
    0lt1
    a1i
    wph
    @18
    c1
    cN
    cle
    wbr
    knoppndvlem7.n
    cN
    nnge1
    syl
    ltletrd
    ltned
    necomd
    mulne0d
    #
    wph
    cJ
    @11
    znegcld
    expclzd
    #
    @17
    @23
    divcld
    wph
    cM
    knoppndvlem7.m
    zcnd
    #
    mulassd
    eqcomd
    wph
    @13
    @15
    cM
    cmul
    wph
    @13
    @2
    @8
    cmul
    co
    #
    c2
    cdiv
    co
    #
    @15
    wph
    @29
    @13
    wph
    @2
    @8
    c2
    @22
    @26
    @17
    @23
    divassd
    eqcomd
    wph
    @28
    c1
    c2
    cdiv
    wph
    @28
    @2
    c1
    @2
    cdiv
    co
    #
    cmul
    co
    c1
    wph
    @8
    @30
    @2
    cmul
    wph
    @1
    cJ
    @21
    @25
    @11
    expnegd
    oveq2d
    wph
    @2
    @22
    wph
    @1
    cJ
    @21
    @25
    @11
    expne0d
    recidd
    eqtrd
    oveq1d
    eqtrd
    oveq1d
    wph
    @5
    @16
    wph
    cM
    c2
    @27
    @17
    @23
    divrec2d
    eqcomd
    3eqtrd
    eqtrd
    fveq2d
    oveq2d
    eqtrd
end
