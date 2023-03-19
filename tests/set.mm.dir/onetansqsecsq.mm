include "cc.mm"
include "wcel.mm"
include "ccos.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "c1.mm"
include "ctan.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "cdiv.mm"
include "csec.mm"
include "csin.mm"
include "wceq.mm"
include "wb.mm"
include "coscl.mm"
include "sqeq0.mm"
include "syl.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "sqcld.mm"
include "divid.mm"
include "sylan.mm"
include "syldan.mm"
include "eqcomd.mm"
include "tanval.mm"
include "oveq1d.mm"
include "cn0.mm"
include "2nn0.mm"
include "sincl.mm"
include "expdiv.mm"
include "syl3an1.mm"
include "mp3an3.mm"
include "3impb.mm"
include "syl3an2.mm"
include "3anidm12.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "divdir.mm"
include "eqtr4d.mm"
include "addcomd.mm"
include "sincossq.mm"
include "eqtr3d.mm"
include "adantr.mm"
include "secval.mm"
include "ax-1cn.mm"
include "mp3an13.mm"
include "sq1.mm"
include "oveq1i.mm"
include "syl6eq.mm"

theorem onetansqsecsq
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. CC /\ ( cos ` A ) =/= 0 ) -> ( 1 + ( ( tan ` A ) ^ 2 ) ) = ( ( sec ` A ) ^ 2 ) )

  proof
    cA
    cc
    wcel
    #
    cA
    ccos
    cfv
    #
    cc0
    wne
    #
    wa
    #
    c1
    cA
    ctan
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    c1
    @1
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cA
    csec
    cfv
    #
    c2
    cexp
    co
    #
    @3
    @6
    @7
    cA
    csin
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    @7
    cdiv
    co
    #
    @8
    @3
    @6
    @7
    @7
    cdiv
    co
    #
    @12
    @7
    cdiv
    co
    #
    caddc
    co
    #
    @14
    @3
    c1
    @15
    @5
    @16
    caddc
    @3
    @15
    c1
    @0
    @2
    @7
    cc0
    wne
    #
    @15
    c1
    wceq
    #
    @0
    @18
    @2
    @0
    @7
    cc0
    @1
    cc0
    @0
    @1
    cc
    wcel
    #
    @7
    cc0
    wceq
    @1
    cc0
    wceq
    wb
    cA
    coscl
    #
    @1
    sqeq0
    syl
    necon3bid
    biimpar
    #
    @0
    @7
    cc
    wcel
    #
    @18
    @19
    @0
    @1
    @21
    sqcld
    #
    @7
    divid
    sylan
    syldan
    eqcomd
    @3
    @5
    @11
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
    @4
    @25
    c2
    cexp
    cA
    tanval
    oveq1d
    @0
    @2
    @26
    @16
    wceq
    #
    @0
    @0
    @20
    @2
    @27
    @21
    @0
    @20
    @2
    @27
    @0
    @20
    @2
    wa
    #
    c2
    cn0
    wcel
    #
    @27
    2nn0
    @0
    @11
    cc
    wcel
    @28
    @29
    @27
    cA
    sincl
    #
    @11
    @1
    c2
    expdiv
    syl3an1
    mp3an3
    3impb
    syl3an2
    3anidm12
    eqtrd
    oveq12d
    @0
    @2
    @18
    @14
    @17
    wceq
    #
    @22
    @0
    @18
    @31
    @0
    @0
    @23
    @18
    @31
    @24
    @0
    @23
    @18
    @31
    @0
    @23
    @18
    wa
    #
    @31
    @0
    @0
    @12
    cc
    wcel
    #
    @32
    @31
    @0
    @11
    @30
    sqcld
    #
    @0
    @23
    @33
    @32
    @31
    @24
    @7
    @12
    @7
    divdir
    syl3an1
    syl3an2
    3anidm12
    3impb
    syl3an2
    3anidm12
    syldan
    eqtr4d
    @0
    @14
    @8
    wceq
    @2
    @0
    @13
    c1
    @7
    cdiv
    @0
    @12
    @7
    caddc
    co
    @13
    c1
    @0
    @12
    @7
    @34
    @24
    addcomd
    cA
    sincossq
    eqtr3d
    oveq1d
    adantr
    eqtrd
    @3
    @10
    c1
    @1
    cdiv
    co
    #
    c2
    cexp
    co
    #
    @8
    @3
    @9
    @35
    c2
    cexp
    cA
    secval
    oveq1d
    @3
    @36
    c1
    c2
    cexp
    co
    #
    @7
    cdiv
    co
    #
    @8
    @0
    @20
    @2
    @36
    @38
    wceq
    #
    @21
    c1
    cc
    wcel
    @28
    @29
    @39
    ax-1cn
    2nn0
    c1
    @1
    c2
    expdiv
    mp3an13
    sylan
    @37
    c1
    @7
    cdiv
    sq1
    oveq1i
    syl6eq
    eqtrd
    eqtr4d
end
