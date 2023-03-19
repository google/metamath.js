include "cusgr.mm"
include "wcel.mm"
include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "w3a.mm"
include "co.mm"
include "cc0.mm"
include "cv.mm"
include "wceq.mm"
include "c2.mm"
include "cmin.mm"
include "wa.mm"
include "cclwwlkn.mm"
include "crab.mm"
include "cop.mm"
include "csubstr.mm"
include "c1.mm"
include "cnbgr.mm"
include "uzuzle23.mm"
include "numclwwlkovg.mm"
include "sylan2.mm"
include "3adant1.mm"
include "simpll3.mm"
include "simplr.mm"
include "simprr.mm"
include "extwwlkfablem.mm"
include "syl3anc.mm"
include "simpl.mm"
include "adantl.mm"
include "jca.mm"
include "simp1.mm"
include "anim1i.mm"
include "adantr.mm"
include "clwwlknlbonbgr1.mm"
include "syl.mm"
include "oveq2.mm"
include "eqcoms.mm"
include "eleqtrrd.mm"
include "simpr.mm"
include "eqtrd.mm"
include "3jca.mm"
include "ex.mm"
include "wi.mm"
include "eqcomd.mm"
include "a1d.mm"
include "3imp.mm"
include "impbid1.mm"
include "cword.mm"
include "chash.mm"
include "cfz.mm"
include "ige3m2fz.mm"
include "eleq2d.mm"
include "syl5ibr.mm"
include "jctild.mm"
include "clwwlknbp.mm"
include "syl11.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "swrd0fv0.mm"
include "eqeq1d.mm"
include "anbi2d.mm"
include "3anbi1d.mm"
include "wb.mm"
include "cclwwlknon.mm"
include "eleq2i.mm"
include "isclwwlknon.mm"
include "a1i.mm"
include "syl5bb.mm"
include "bicomd.mm"
include "3bitrd.mm"
include "rabbidva.mm"

theorem extwwlkfab
  let vw: setvar w
  let vv: setvar v
  let cC: class C
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  assume extwwlkfab.v: |- V = ( Vtx ` G )
  assume extwwlkfab.c: |- C = ( v e. V , n e. ( ZZ>= ` 2 ) |-> { w e. ( n ClWWalksN G ) | ( ( w ` 0 ) = v /\ ( w ` ( n - 2 ) ) = ( w ` 0 ) ) } )
  assume extwwlkfab.f: |- F = ( X ( ClWWalksNOn ` G ) ( N - 2 ) )

  disjoint G n
  disjoint G v
  disjoint G w
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint V n
  disjoint V v
  disjoint V w
  disjoint X n
  disjoint X v
  disjoint X w
  disjoint N n
  disjoint N v
  disjoint N w
  assert |- ( ( G e. USGraph /\ X e. V /\ N e. ( ZZ>= ` 3 ) ) -> ( X C N ) = { w e. ( N ClWWalksN G ) | ( ( w substr <. 0 , ( N - 2 ) >. ) e. F /\ ( w ` ( N - 1 ) ) e. ( G NeighbVtx X ) /\ ( w ` ( N - 2 ) ) = X ) } )

  proof
    cG
    cusgr
    wcel
    #
    cX
    cV
    wcel
    #
    cN
    c3
    cuz
    cfv
    wcel
    #
    w3a
    #
    cX
    cN
    cC
    co
    #
    cc0
    vw
    cv
    #
    cfv
    #
    cX
    wceq
    #
    cN
    c2
    cmin
    co
    #
    @5
    cfv
    #
    @6
    wceq
    #
    wa
    #
    vw
    cN
    cG
    cclwwlkn
    co
    #
    crab
    #
    @5
    cc0
    @8
    cop
    csubstr
    co
    #
    cF
    wcel
    #
    cN
    c1
    cmin
    co
    @5
    cfv
    #
    cG
    cX
    cnbgr
    co
    #
    wcel
    #
    @9
    cX
    wceq
    #
    w3a
    #
    vw
    @12
    crab
    @1
    @2
    @4
    @13
    wceq
    #
    @0
    @2
    @1
    cN
    c2
    cuz
    cfv
    wcel
    @21
    cN
    uzuzle23
    vw
    vv
    cC
    vn
    cG
    cN
    cV
    cX
    extwwlkfab.c
    numclwwlkovg
    sylan2
    3adant1
    @3
    @11
    @20
    vw
    @12
    @3
    @5
    @12
    wcel
    #
    wa
    #
    @11
    @14
    @8
    cG
    cclwwlkn
    co
    wcel
    #
    @7
    wa
    #
    @18
    @19
    w3a
    #
    @24
    cc0
    @14
    cfv
    #
    cX
    wceq
    #
    wa
    #
    @18
    @19
    w3a
    #
    @20
    @23
    @11
    @26
    @23
    @11
    @26
    @23
    @11
    wa
    #
    @25
    @18
    @19
    @31
    @24
    @7
    @31
    @2
    @22
    @10
    @24
    @0
    @1
    @2
    @22
    @11
    simpll3
    @3
    @22
    @11
    simplr
    @23
    @7
    @10
    simprr
    vw
    cG
    cN
    extwwlkfablem
    syl3anc
    @11
    @7
    @23
    @7
    @10
    simpl
    #
    adantl
    jca
    @31
    @16
    cG
    @6
    cnbgr
    co
    #
    @17
    @31
    @0
    @22
    wa
    #
    @16
    @33
    wcel
    @23
    @34
    @11
    @3
    @0
    @22
    @0
    @1
    @2
    simp1
    anim1i
    adantr
    cG
    cN
    @5
    clwwlknlbonbgr1
    syl
    @11
    @17
    @33
    wceq
    #
    @23
    @7
    @35
    @10
    @35
    cX
    @6
    cX
    @6
    cG
    cnbgr
    oveq2
    eqcoms
    adantr
    adantl
    eleqtrrd
    @11
    @19
    @23
    @11
    @9
    @6
    cX
    @7
    @10
    simpr
    @32
    eqtrd
    adantl
    3jca
    ex
    @25
    @18
    @19
    @11
    @7
    @18
    @19
    @11
    wi
    #
    wi
    @24
    @7
    @36
    @18
    @7
    @19
    @11
    @7
    @19
    wa
    #
    @7
    @10
    @7
    @19
    simpl
    #
    @37
    @9
    cX
    @6
    @7
    @19
    simpr
    @37
    @6
    cX
    @38
    eqcomd
    eqtrd
    jca
    ex
    a1d
    adantl
    3imp
    impbid1
    @23
    @25
    @29
    @18
    @19
    @23
    @7
    @28
    @24
    @23
    @6
    @27
    cX
    @23
    @27
    @6
    @23
    @5
    cV
    cword
    wcel
    #
    @8
    c1
    @5
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    @27
    @6
    wceq
    @3
    @22
    @43
    @2
    @0
    @22
    @43
    wi
    @1
    @39
    @40
    cN
    wceq
    #
    wa
    #
    @2
    @43
    @22
    @45
    @2
    @42
    @39
    @44
    @2
    @42
    wi
    @39
    @2
    @42
    @44
    @8
    c1
    cN
    cfz
    co
    #
    wcel
    cN
    ige3m2fz
    @44
    @41
    @46
    @8
    @40
    cN
    c1
    cfz
    oveq2
    eleq2d
    syl5ibr
    adantl
    @39
    @44
    simpl
    jctild
    cG
    cN
    cV
    @5
    extwwlkfab.v
    clwwlknbp
    syl11
    3ad2ant3
    imp
    @8
    cV
    @5
    swrd0fv0
    syl
    eqcomd
    eqeq1d
    anbi2d
    3anbi1d
    @3
    @30
    @20
    wb
    @22
    @3
    @20
    @30
    @3
    @15
    @29
    @18
    @19
    @15
    @14
    cX
    @8
    cG
    cclwwlknon
    cfv
    co
    #
    wcel
    #
    @3
    @29
    cF
    @47
    @14
    extwwlkfab.f
    eleq2i
    @48
    @29
    wb
    @3
    cG
    @8
    @14
    cX
    isclwwlknon
    a1i
    syl5bb
    3anbi1d
    bicomd
    adantr
    3bitrd
    rabbidva
    eqtrd
end
