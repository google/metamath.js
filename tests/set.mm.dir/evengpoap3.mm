include "c1.mm"
include "c2.mm"
include "cdc.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "ceven.mm"
include "wa.mm"
include "c7.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cgbo.mm"
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
include "cc0.mm"
include "7p3e10.mm"
include "1nn0.mm"
include "0nn0.mm"
include "2nn.mm"
include "2pos.mm"
include "declt.mm"
include "eqbrtri.mm"
include "cr.mm"
include "7re.mm"
include "3re.mm"
include "readdcli.mm"
include "2nn0.mm"
include "deccl.mm"
include "nn0rei.mm"
include "zre.mm"
include "ltletr.mm"
include "mp3an12i.mm"
include "mpani.mm"
include "imp.mm"
include "3adant1.mm"
include "3ad2ant2.mm"
include "ltaddsubd.mm"
include "mpbid.mm"
include "sylbi.mm"
include "adantr.mm"
include "simpr.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "cc.mm"
include "eluzelcn.mm"
include "3cn.mm"
include "jctir.mm"
include "npcan.mm"
include "eqcomd.mm"
include "rspcedvd.mm"
include "ex.mm"
include "embantd.mm"
include "syldc.mm"

theorem evengpoap3
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
  assert |- ( A. m e. Odd ( 7 < m -> m e. GoldbachOdd ) -> ( ( N e. ( ZZ>= ` ; 1 2 ) /\ N e. Even ) -> E. o e. GoldbachOdd N = ( o + 3 ) ) )

  proof
    cN
    c1
    c2
    cdc
    #
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
    c7
    vm
    cv
    #
    clt
    wbr
    #
    @4
    cgbo
    wcel
    #
    wi
    #
    vm
    codd
    wral
    c7
    cN
    c3
    cmin
    co
    #
    clt
    wbr
    #
    @8
    cgbo
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
    cgbo
    wrex
    #
    @3
    @7
    @11
    vm
    @8
    codd
    @3
    @2
    c3
    codd
    wcel
    #
    wa
    @8
    codd
    wcel
    @3
    @16
    @2
    @1
    @16
    @2
    @16
    @1
    3odd
    a1i
    anim1i
    ancomd
    cN
    c3
    emoo
    syl
    @4
    @8
    wceq
    #
    @7
    @11
    wb
    @3
    @17
    @5
    @9
    @6
    @10
    @4
    @8
    c7
    clt
    breq2
    @4
    @8
    cgbo
    eleq1
    imbi12d
    adantl
    rspcdv
    @3
    @9
    @10
    @15
    @1
    @9
    @2
    @1
    @0
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @0
    cN
    cle
    wbr
    #
    w3a
    #
    @9
    @0
    cN
    eluz2
    @21
    c7
    c3
    caddc
    co
    #
    cN
    clt
    wbr
    #
    @9
    @19
    @20
    @23
    @18
    @19
    @20
    @23
    @19
    @22
    @0
    clt
    wbr
    #
    @20
    @23
    @22
    c1
    cc0
    cdc
    @0
    clt
    7p3e10
    c1
    cc0
    c2
    1nn0
    0nn0
    2nn
    2pos
    declt
    eqbrtri
    @22
    cr
    wcel
    @0
    cr
    wcel
    @19
    cN
    cr
    wcel
    #
    @24
    @20
    wa
    @23
    wi
    c7
    c3
    7re
    3re
    readdcli
    @0
    c1
    c2
    1nn0
    2nn0
    deccl
    nn0rei
    cN
    zre
    #
    @22
    @0
    cN
    ltletr
    mp3an12i
    mpani
    imp
    3adant1
    @21
    c7
    c3
    cN
    c7
    cr
    wcel
    @21
    7re
    a1i
    c3
    cr
    wcel
    @21
    3re
    a1i
    @19
    @18
    @25
    @20
    @26
    3ad2ant2
    ltaddsubd
    mpbid
    sylbi
    adantr
    @3
    @10
    @15
    @3
    @10
    wa
    #
    @14
    cN
    @8
    c3
    caddc
    co
    #
    wceq
    #
    vo
    @8
    cgbo
    @3
    @10
    simpr
    @12
    @8
    wceq
    #
    @14
    @29
    wb
    @27
    @30
    @13
    @28
    cN
    @12
    @8
    c3
    caddc
    oveq1
    eqeq2d
    adantl
    @27
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
    @29
    @3
    @33
    @10
    @1
    @33
    @2
    @1
    @31
    @32
    @0
    cN
    eluzelcn
    3cn
    jctir
    adantr
    adantr
    @33
    @28
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
