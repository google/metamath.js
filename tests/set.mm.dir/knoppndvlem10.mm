include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cexp.mm"
include "c2.mm"
include "cdiv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "cneg.mm"
include "cioo.mm"
include "wcel.mm"
include "adantr.mm"
include "cn0.mm"
include "cz.mm"
include "peano2zd.mm"
include "cn.mm"
include "wn.mm"
include "notnot.mm"
include "adantl.mm"
include "wb.mm"
include "oddp1even.mm"
include "syl.mm"
include "mtbid.mm"
include "knoppndvlem9.mm"
include "notnotrd.mm"
include "knoppndvlem8.mm"
include "oveq12d.mm"
include "cr.mm"
include "clt.mm"
include "knoppndvlem3.mm"
include "simpld.mm"
include "recnd.mm"
include "expcld.mm"
include "2cnd.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "divcld.mm"
include "subid1d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "cmul.mm"
include "nn0zd.mm"
include "knoppndvlem1.mm"
include "eqeltrd.mm"
include "knoppcnlem3.mm"
include "abssubd.mm"
include "simpr.mm"
include "mpbid.mm"
include "pm2.61dan.mm"
include "absdivd.mm"
include "absexpd.mm"
include "cle.mm"
include "0le2.mm"
include "2re.mm"
include "absidi.mm"
include "ax-mp.mm"

theorem knoppndvlem10
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cT: class T
  let vn: setvar n
  let cF: class F
  let cJ: class J
  let cM: class M
  let cN: class N
  assume knoppndvlem10.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppndvlem10.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppndvlem10.a: |- A = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. M )
  assume knoppndvlem10.b: |- B = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. ( M + 1 ) )
  assume knoppndvlem10.c: |- ( ph -> C e. ( -u 1 (,) 1 ) )
  assume knoppndvlem10.j: |- ( ph -> J e. NN0 )
  assume knoppndvlem10.m: |- ( ph -> M e. ZZ )
  assume knoppndvlem10.n: |- ( ph -> N e. NN )

  disjoint A n
  disjoint A y
  disjoint n y
  disjoint A x
  disjoint B n
  disjoint B y
  disjoint B x
  disjoint C n
  disjoint C y
  disjoint J n
  disjoint J x
  disjoint M n
  disjoint M y
  disjoint M x
  disjoint N n
  disjoint N y
  disjoint N x
  disjoint T n
  disjoint T y
  disjoint n ph
  disjoint ph y
  assert |- ( ph -> ( abs ` ( ( ( F ` B ) ` J ) - ( ( F ` A ) ` J ) ) ) = ( ( ( abs ` C ) ^ J ) / 2 ) )

  proof
    wph
    cJ
    cB
    cF
    cfv
    cfv
    #
    cJ
    cA
    cF
    cfv
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cC
    cJ
    cexp
    co
    #
    c2
    cdiv
    co
    #
    cabs
    cfv
    #
    cC
    cabs
    cfv
    #
    cJ
    cexp
    co
    #
    c2
    cdiv
    co
    #
    wph
    c2
    cM
    cdvds
    wbr
    #
    @3
    @6
    wceq
    wph
    @10
    wa
    #
    @2
    @5
    cabs
    @11
    @2
    @5
    cc0
    cmin
    co
    #
    @5
    @11
    @0
    @5
    @1
    cc0
    cmin
    @11
    vx
    vy
    cB
    cC
    cT
    vn
    cF
    cJ
    cM
    c1
    caddc
    co
    #
    cN
    knoppndvlem10.t
    knoppndvlem10.f
    knoppndvlem10.b
    wph
    cC
    c1
    cneg
    c1
    cioo
    co
    wcel
    #
    @10
    knoppndvlem10.c
    adantr
    #
    wph
    cJ
    cn0
    wcel
    #
    @10
    knoppndvlem10.j
    adantr
    #
    wph
    @13
    cz
    wcel
    #
    @10
    wph
    cM
    knoppndvlem10.m
    peano2zd
    #
    adantr
    wph
    cN
    cn
    wcel
    #
    @10
    knoppndvlem10.n
    adantr
    #
    @11
    @10
    wn
    #
    c2
    @13
    cdvds
    wbr
    #
    @10
    @22
    wn
    wph
    @10
    notnot
    adantl
    #
    @11
    cM
    cz
    wcel
    #
    @22
    @23
    wb
    #
    wph
    @25
    @10
    knoppndvlem10.m
    adantr
    #
    cM
    oddp1even
    #
    syl
    mtbid
    knoppndvlem9
    @11
    vx
    vy
    cA
    cC
    cT
    vn
    cF
    cJ
    cM
    cN
    knoppndvlem10.t
    knoppndvlem10.f
    knoppndvlem10.a
    @15
    @17
    @27
    @21
    @11
    @10
    @24
    notnotrd
    knoppndvlem8
    oveq12d
    wph
    @12
    @5
    wceq
    #
    @10
    wph
    @5
    wph
    @4
    c2
    wph
    cC
    cJ
    wph
    cC
    wph
    cC
    cr
    wcel
    @7
    c1
    clt
    wbr
    wph
    cC
    knoppndvlem10.c
    knoppndvlem3
    simpld
    #
    recnd
    #
    knoppndvlem10.j
    expcld
    #
    wph
    2cnd
    #
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    #
    divcld
    subid1d
    #
    adantr
    eqtrd
    fveq2d
    wph
    @22
    wa
    #
    @3
    @1
    @0
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    wph
    @3
    @38
    wceq
    @22
    wph
    @0
    @1
    wph
    @0
    wph
    vx
    vy
    cB
    cC
    cT
    vn
    cF
    cJ
    cN
    knoppndvlem10.t
    knoppndvlem10.f
    knoppndvlem10.n
    @30
    wph
    cB
    c2
    cN
    cmul
    co
    cJ
    cneg
    cexp
    co
    c2
    cdiv
    co
    #
    @13
    cmul
    co
    #
    cr
    cB
    @40
    wceq
    wph
    knoppndvlem10.b
    a1i
    wph
    cJ
    @13
    cN
    knoppndvlem10.n
    wph
    cJ
    knoppndvlem10.j
    nn0zd
    #
    @19
    knoppndvlem1
    eqeltrd
    knoppndvlem10.j
    knoppcnlem3
    recnd
    wph
    @1
    wph
    vx
    vy
    cA
    cC
    cT
    vn
    cF
    cJ
    cN
    knoppndvlem10.t
    knoppndvlem10.f
    knoppndvlem10.n
    @30
    wph
    cA
    @39
    cM
    cmul
    co
    #
    cr
    cA
    @42
    wceq
    wph
    knoppndvlem10.a
    a1i
    wph
    cJ
    cM
    cN
    knoppndvlem10.n
    @41
    knoppndvlem10.m
    knoppndvlem1
    eqeltrd
    knoppndvlem10.j
    knoppcnlem3
    recnd
    abssubd
    adantr
    @36
    @37
    @5
    cabs
    @36
    @37
    @12
    @5
    @36
    @1
    @5
    @0
    cc0
    cmin
    @36
    vx
    vy
    cA
    cC
    cT
    vn
    cF
    cJ
    cM
    cN
    knoppndvlem10.t
    knoppndvlem10.f
    knoppndvlem10.a
    wph
    @14
    @22
    knoppndvlem10.c
    adantr
    #
    wph
    @16
    @22
    knoppndvlem10.j
    adantr
    #
    wph
    @25
    @22
    knoppndvlem10.m
    adantr
    #
    wph
    @20
    @22
    knoppndvlem10.n
    adantr
    #
    wph
    @22
    simpr
    #
    knoppndvlem9
    @36
    vx
    vy
    cB
    cC
    cT
    vn
    cF
    cJ
    @13
    cN
    knoppndvlem10.t
    knoppndvlem10.f
    knoppndvlem10.b
    @43
    @44
    wph
    @18
    @22
    @19
    adantr
    @46
    @36
    @22
    @23
    @47
    @36
    @25
    @26
    @45
    @28
    syl
    mpbid
    knoppndvlem8
    oveq12d
    wph
    @29
    @22
    @35
    adantr
    eqtrd
    fveq2d
    eqtrd
    pm2.61dan
    wph
    @6
    @4
    cabs
    cfv
    #
    c2
    cabs
    cfv
    #
    cdiv
    co
    @9
    wph
    @4
    c2
    @32
    @33
    @34
    absdivd
    wph
    @48
    @8
    @49
    c2
    cdiv
    wph
    cC
    cJ
    @31
    knoppndvlem10.j
    absexpd
    @49
    c2
    wceq
    #
    wph
    cc0
    c2
    cle
    wbr
    @50
    0le2
    c2
    2re
    absidi
    ax-mp
    a1i
    oveq12d
    eqtrd
    eqtrd
end
