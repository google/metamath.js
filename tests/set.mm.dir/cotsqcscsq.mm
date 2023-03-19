include "cc.mm"
include "wcel.mm"
include "csin.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "c1.mm"
include "ccot.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "ccos.mm"
include "cdiv.mm"
include "ccsc.mm"
include "cotval.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "wceq.mm"
include "sincossq.mm"
include "adantr.mm"
include "sincl.mm"
include "sqcld.mm"
include "wb.mm"
include "sqne0.mm"
include "syl.mm"
include "biimpar.mm"
include "dividd.mm"
include "coscl.mm"
include "divdird.mm"
include "jca.mm"
include "cn0.mm"
include "2nn0.mm"
include "expdiv.mm"
include "mp3an3.mm"
include "anassrs.mm"
include "sylan.mm"
include "3eqtr4rd.mm"
include "cscval.mm"
include "ax-1cn.mm"
include "mp3an13.mm"
include "sq1.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "eqtr4d.mm"

theorem cotsqcscsq
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. CC /\ ( sin ` A ) =/= 0 ) -> ( 1 + ( ( cot ` A ) ^ 2 ) ) = ( ( csc ` A ) ^ 2 ) )

  proof
    cA
    cc
    wcel
    #
    cA
    csin
    cfv
    #
    cc0
    wne
    #
    wa
    #
    c1
    cA
    ccot
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    c1
    cA
    ccos
    cfv
    #
    @1
    cdiv
    co
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    cA
    ccsc
    cfv
    #
    c2
    cexp
    co
    #
    @3
    @5
    @8
    c1
    caddc
    @3
    @4
    @7
    c2
    cexp
    cA
    cotval
    oveq1d
    oveq2d
    @3
    @1
    c2
    cexp
    co
    #
    @6
    c2
    cexp
    co
    #
    caddc
    co
    #
    @12
    cdiv
    co
    #
    c1
    @12
    cdiv
    co
    #
    @9
    @11
    @0
    @15
    @16
    wceq
    @2
    @0
    @14
    c1
    @12
    cdiv
    cA
    sincossq
    oveq1d
    adantr
    @3
    @12
    @12
    cdiv
    co
    #
    @13
    @12
    cdiv
    co
    #
    caddc
    co
    c1
    @18
    caddc
    co
    @15
    @9
    @3
    @17
    c1
    @18
    caddc
    @3
    @12
    @0
    @12
    cc
    wcel
    @2
    @0
    @1
    cA
    sincl
    #
    sqcld
    adantr
    #
    @0
    @12
    cc0
    wne
    #
    @2
    @0
    @1
    cc
    wcel
    #
    @21
    @2
    wb
    @19
    @1
    sqne0
    syl
    biimpar
    #
    dividd
    oveq1d
    @3
    @12
    @13
    @12
    @20
    @0
    @13
    cc
    wcel
    @2
    @0
    @6
    cA
    coscl
    #
    sqcld
    adantr
    @20
    @23
    divdird
    @3
    @8
    @18
    c1
    caddc
    @0
    @6
    cc
    wcel
    #
    @22
    wa
    @2
    @8
    @18
    wceq
    #
    @0
    @25
    @22
    @24
    @19
    jca
    @25
    @22
    @2
    @26
    @25
    @22
    @2
    wa
    #
    c2
    cn0
    wcel
    #
    @26
    2nn0
    @6
    @1
    c2
    expdiv
    mp3an3
    anassrs
    sylan
    oveq2d
    3eqtr4rd
    @3
    @11
    c1
    @1
    cdiv
    co
    #
    c2
    cexp
    co
    #
    @16
    @3
    @10
    @29
    c2
    cexp
    cA
    cscval
    oveq1d
    @3
    @30
    c1
    c2
    cexp
    co
    #
    @12
    cdiv
    co
    #
    @16
    @0
    @22
    @2
    @30
    @32
    wceq
    #
    @19
    c1
    cc
    wcel
    @27
    @28
    @33
    ax-1cn
    2nn0
    c1
    @1
    c2
    expdiv
    mp3an13
    sylan
    @31
    c1
    @12
    cdiv
    sq1
    oveq1i
    syl6eq
    eqtrd
    3eqtr4rd
    eqtr4d
end
