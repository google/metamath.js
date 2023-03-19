include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cmul.mm"
include "c1.mm"
include "knoppndvlem7.mm"
include "cv.mm"
include "caddc.mm"
include "wceq.mm"
include "cz.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wrex.mm"
include "wcel.mm"
include "wb.mm"
include "odd2np1.mm"
include "syl.mm"
include "mpbid.mm"
include "wa.mm"
include "eqcom.mm"
include "biimpi.mm"
include "oveq1d.mm"
include "adantl.mm"
include "2cnd.mm"
include "cc.mm"
include "zcn.mm"
include "mulcld.mm"
include "1cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "divdird.mm"
include "divcan3d.mm"
include "eqtrd.mm"
include "adantrr.mm"
include "fveq2d.mm"
include "id.mm"
include "dnizphlfeqhlf.mm"
include "rexlimddv.mm"
include "oveq2d.mm"
include "cr.mm"
include "cabs.mm"
include "clt.mm"
include "knoppndvlem3.mm"
include "simpld.mm"
include "recnd.mm"
include "expcld.mm"
include "div12d.mm"
include "divcld.mm"
include "mulid2d.mm"
include "3eqtrd.mm"

theorem knoppndvlem9
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
  let vm: setvar m
  assume knoppndvlem9.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppndvlem9.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppndvlem9.a: |- A = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. M )
  assume knoppndvlem9.c: |- ( ph -> C e. ( -u 1 (,) 1 ) )
  assume knoppndvlem9.j: |- ( ph -> J e. NN0 )
  assume knoppndvlem9.m: |- ( ph -> M e. ZZ )
  assume knoppndvlem9.n: |- ( ph -> N e. NN )
  assume knoppndvlem9.1: |- ( ph -> -. 2 || M )

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
  disjoint M m
  disjoint T m
  disjoint m ph
  disjoint m x
  assert |- ( ph -> ( ( F ` A ) ` J ) = ( ( C ^ J ) / 2 ) )

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
    c1
    c2
    cdiv
    co
    #
    cmul
    co
    #
    @0
    c2
    cdiv
    co
    #
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
    knoppndvlem9.t
    knoppndvlem9.f
    knoppndvlem9.a
    knoppndvlem9.j
    knoppndvlem9.m
    knoppndvlem9.n
    knoppndvlem7
    wph
    @2
    @3
    @0
    cmul
    wph
    c2
    vm
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    cM
    wceq
    #
    @2
    @3
    wceq
    vm
    cz
    wph
    c2
    cM
    cdvds
    wbr
    wn
    #
    @9
    vm
    cz
    wrex
    #
    knoppndvlem9.1
    wph
    cM
    cz
    wcel
    @10
    @11
    wb
    knoppndvlem9.m
    vm
    cM
    odd2np1
    syl
    mpbid
    wph
    @6
    cz
    wcel
    #
    @9
    wa
    #
    wa
    #
    @2
    @6
    @3
    caddc
    co
    #
    cT
    cfv
    #
    @3
    @14
    @1
    @15
    cT
    @14
    @1
    @8
    c2
    cdiv
    co
    #
    @15
    @13
    @1
    @17
    wceq
    #
    wph
    @9
    @18
    @12
    @9
    cM
    @8
    c2
    cdiv
    @9
    cM
    @8
    wceq
    @8
    cM
    eqcom
    biimpi
    oveq1d
    adantl
    adantl
    wph
    @12
    @17
    @15
    wceq
    @9
    wph
    @12
    wa
    #
    @17
    @7
    c2
    cdiv
    co
    #
    @3
    caddc
    co
    @15
    @19
    @7
    c1
    c2
    @19
    c2
    @6
    @19
    2cnd
    #
    @12
    @6
    cc
    wcel
    wph
    @6
    zcn
    adantl
    #
    mulcld
    @19
    1cnd
    @21
    c2
    cc0
    wne
    #
    @19
    2ne0
    a1i
    #
    divdird
    @19
    @20
    @6
    @3
    caddc
    @19
    @6
    c2
    @22
    @21
    @24
    divcan3d
    oveq1d
    eqtrd
    adantrr
    eqtrd
    fveq2d
    wph
    @12
    @16
    @3
    wceq
    #
    @9
    @12
    @25
    wph
    @12
    vx
    @6
    cT
    knoppndvlem9.t
    @12
    id
    dnizphlfeqhlf
    adantl
    adantrr
    eqtrd
    rexlimddv
    oveq2d
    wph
    @4
    c1
    @5
    cmul
    co
    @5
    wph
    @0
    c1
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
    cC
    cabs
    cfv
    c1
    clt
    wbr
    wph
    cC
    knoppndvlem9.c
    knoppndvlem3
    simpld
    recnd
    knoppndvlem9.j
    expcld
    #
    wph
    1cnd
    wph
    2cnd
    #
    @23
    wph
    2ne0
    a1i
    #
    div12d
    wph
    @5
    wph
    @0
    c2
    @26
    @27
    @28
    divcld
    mulid2d
    eqtrd
    3eqtrd
end
