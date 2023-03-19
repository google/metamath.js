include "c9.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "ceven.mm"
include "wa.mm"
include "c5.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cgbow.mm"
include "wi.mm"
include "codd.mm"
include "wral.mm"
include "c3.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "wrex.mm"
include "3odd.mm"
include "a1i.mm"
include "anim1i.mm"
include "ancomd.mm"
include "emoo.mm"
include "syl.mm"
include "wb.mm"
include "breq2.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "adantl.mm"
include "rspcdv.mm"
include "cz.mm"
include "cle.mm"
include "w3a.mm"
include "eluz2.mm"
include "c1.mm"
include "c8.mm"
include "5p3e8.mm"
include "8p1e9.mm"
include "9cn.mm"
include "ax-1cn.mm"
include "8cn.mm"
include "subadd2i.mm"
include "mpbir.mm"
include "eqtr4i.mm"
include "zlem1lt.mm"
include "biimp3a.mm"
include "syl5eqbr.mm"
include "cr.mm"
include "5re.mm"
include "3re.mm"
include "zre.mm"
include "3jca.mm"
include "3ad2ant2.mm"
include "ltaddsub.mm"
include "mpbid.mm"
include "sylbi.mm"
include "adantr.mm"
include "simpr.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "cc.mm"
include "eluzelcn.mm"
include "3cn.mm"
include "jca.mm"
include "npcan.mm"
include "eqcomd.mm"
include "rspcedvd.mm"
include "ex.mm"
include "embantd.mm"
include "syldc.mm"

theorem evengpop3
  let vm: setvar m
  let vo: setvar o
  let cN: class N
  let vf: setvar f
  let vk: setvar k
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vx: setvar x

  disjoint N m
  disjoint N o
  disjoint N f
  disjoint N k
  disjoint N p
  disjoint N q
  disjoint N r
  disjoint f k
  disjoint f m
  disjoint f p
  disjoint f q
  disjoint f r
  disjoint k m
  disjoint k p
  disjoint k q
  disjoint k r
  disjoint m p
  disjoint m q
  disjoint m r
  disjoint p q
  disjoint p r
  disjoint q r
  disjoint k x
  assert |- ( A. m e. Odd ( 5 < m -> m e. GoldbachOddW ) -> ( ( N e. ( ZZ>= ` 9 ) /\ N e. Even ) -> E. o e. GoldbachOddW N = ( o + 3 ) ) )

  proof
    cN
    c9
    cuz
    cfv
    wcel
    #
    cN
    ceven
    wcel
    #
    wa
    #
    c5
    vm
    cv
    #
    clt
    wbr
    #
    @3
    cgbow
    wcel
    #
    wi
    #
    vm
    codd
    wral
    c5
    cN
    c3
    cmin
    co
    #
    clt
    wbr
    #
    @7
    cgbow
    wcel
    #
    wi
    #
    cN
    vo
    cv
    #
    c3
    caddc
    co
    #
    wceq
    #
    vo
    cgbow
    wrex
    #
    @2
    @6
    @10
    vm
    @7
    codd
    @2
    @1
    c3
    codd
    wcel
    #
    wa
    @7
    codd
    wcel
    @2
    @15
    @1
    @0
    @15
    @1
    @15
    @0
    3odd
    a1i
    anim1i
    ancomd
    cN
    c3
    emoo
    syl
    @3
    @7
    wceq
    #
    @6
    @10
    wb
    @2
    @16
    @4
    @8
    @5
    @9
    @3
    @7
    c5
    clt
    breq2
    @3
    @7
    cgbow
    eleq1
    imbi12d
    adantl
    rspcdv
    @2
    @8
    @9
    @14
    @0
    @8
    @1
    @0
    c9
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    c9
    cN
    cle
    wbr
    #
    w3a
    #
    @8
    c9
    cN
    eluz2
    @20
    c5
    c3
    caddc
    co
    #
    cN
    clt
    wbr
    #
    @8
    @20
    @21
    c9
    c1
    cmin
    co
    #
    cN
    clt
    @21
    c8
    @23
    5p3e8
    @23
    c8
    wceq
    c8
    c1
    caddc
    co
    c9
    wceq
    8p1e9
    c9
    c1
    c8
    9cn
    ax-1cn
    8cn
    subadd2i
    mpbir
    eqtr4i
    @17
    @18
    @19
    @23
    cN
    clt
    wbr
    c9
    cN
    zlem1lt
    biimp3a
    syl5eqbr
    @20
    c5
    cr
    wcel
    #
    c3
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    w3a
    #
    @22
    @8
    wb
    @18
    @17
    @27
    @19
    @18
    @24
    @25
    @26
    @24
    @18
    5re
    a1i
    @25
    @18
    3re
    a1i
    cN
    zre
    3jca
    3ad2ant2
    c5
    c3
    cN
    ltaddsub
    syl
    mpbid
    sylbi
    adantr
    @2
    @9
    @14
    @2
    @9
    wa
    #
    @13
    cN
    @7
    c3
    caddc
    co
    #
    wceq
    #
    vo
    @7
    cgbow
    @2
    @9
    simpr
    @11
    @7
    wceq
    #
    @13
    @30
    wb
    @28
    @31
    @12
    @29
    cN
    @11
    @7
    c3
    caddc
    oveq1
    eqeq2d
    adantl
    @28
    cN
    cc
    wcel
    #
    c3
    cc
    wcel
    #
    wa
    #
    @30
    @2
    @34
    @9
    @0
    @34
    @1
    @0
    @32
    @33
    c9
    cN
    eluzelcn
    @33
    @0
    3cn
    a1i
    jca
    adantr
    adantr
    @34
    @29
    cN
    cN
    c3
    npcan
    eqcomd
    syl
    rspcedvd
    ex
    embantd
    syldc
end
