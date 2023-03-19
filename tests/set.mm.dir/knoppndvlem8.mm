include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cmul.mm"
include "cc0.mm"
include "knoppndvlem7.mm"
include "cdvds.mm"
include "wbr.mm"
include "cz.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "wb.mm"
include "2z.mm"
include "a1i.mm"
include "2ne0.mm"
include "3jca.mm"
include "dvdsval2.mm"
include "syl.mm"
include "mpbid.mm"
include "dnizeq0.mm"
include "oveq2d.mm"
include "cr.mm"
include "cabs.mm"
include "c1.mm"
include "clt.mm"
include "knoppndvlem3.mm"
include "simpld.mm"
include "recnd.mm"
include "expcld.mm"
include "mul01d.mm"
include "3eqtrd.mm"

theorem knoppndvlem8
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
  assume knoppndvlem8.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppndvlem8.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppndvlem8.a: |- A = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. M )
  assume knoppndvlem8.c: |- ( ph -> C e. ( -u 1 (,) 1 ) )
  assume knoppndvlem8.j: |- ( ph -> J e. NN0 )
  assume knoppndvlem8.m: |- ( ph -> M e. ZZ )
  assume knoppndvlem8.n: |- ( ph -> N e. NN )
  assume knoppndvlem8.1: |- ( ph -> 2 || M )

  disjoint A n
  disjoint A y
  disjoint n y
  disjoint C n
  disjoint C y
  disjoint J n
  disjoint M x
  disjoint N n
  disjoint N y
  disjoint T n
  disjoint T y
  disjoint n ph
  disjoint ph y
  assert |- ( ph -> ( ( F ` A ) ` J ) = 0 )

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
    @0
    cc0
    cmul
    co
    cc0
    wph
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
    knoppndvlem8.t
    knoppndvlem8.f
    knoppndvlem8.a
    knoppndvlem8.j
    knoppndvlem8.m
    knoppndvlem8.n
    knoppndvlem7
    wph
    @2
    cc0
    @0
    cmul
    wph
    vx
    @1
    cT
    knoppndvlem8.t
    wph
    c2
    cM
    cdvds
    wbr
    #
    @1
    cz
    wcel
    #
    knoppndvlem8.1
    wph
    c2
    cz
    wcel
    #
    c2
    cc0
    wne
    #
    cM
    cz
    wcel
    #
    w3a
    @3
    @4
    wb
    wph
    @5
    @6
    @7
    @5
    wph
    2z
    a1i
    @6
    wph
    2ne0
    a1i
    knoppndvlem8.m
    3jca
    c2
    cM
    dvdsval2
    syl
    mpbid
    dnizeq0
    oveq2d
    wph
    @0
    wph
    cC
    cJ
    wph
    cC
    wph
    cC
    cr
    wcel
    cC
    cabs
    cfv
    c1
    clt
    wbr
    wph
    cC
    knoppndvlem8.c
    knoppndvlem3
    simpld
    recnd
    knoppndvlem8.j
    expcld
    mul01d
    3eqtrd
end
