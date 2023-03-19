include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cwwlksn.mm"
include "wa.mm"
include "cc0.mm"
include "cfv.mm"
include "wceq.mm"
include "cop.mm"
include "csubstr.mm"
include "cv.mm"
include "clsw.mm"
include "cpr.mm"
include "w3a.mm"
include "wrex.mm"
include "wi.mm"
include "wwlksnredwwlkn.mm"
include "imp.mm"
include "simpl.mm"
include "adantl.mm"
include "fveq1.mm"
include "eqcoms.mm"
include "adantr.mm"
include "cvtx.mm"
include "cword.mm"
include "chash.mm"
include "cfz.mm"
include "cfzo.mm"
include "wral.mm"
include "eqid.mm"
include "wwlknp.mm"
include "cn.mm"
include "cle.mm"
include "wbr.mm"
include "nn0p1nn.mm"
include "cr.mm"
include "peano2nn0.mm"
include "nn0re.mm"
include "lep1.mm"
include "3syl.mm"
include "cz.mm"
include "wb.mm"
include "nn0zd.mm"
include "fznn.mm"
include "mpbir2and.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "syl5ibr.mm"
include "jctild.mm"
include "3adant3.mm"
include "syl.mm"
include "impcom.mm"
include "swrd0fv0.mm"
include "simprll.mm"
include "3eqtrd.mm"
include "ex.mm"
include "simpr.mm"
include "3jca.mm"
include "reximdva.mm"
include "com13.mm"
include "mpcom.mm"
include "eqcomd.mm"
include "com12.mm"
include "rexlimdvw.mm"
include "impbid.mm"

theorem wwlksnredwwlkn0
  let vy: setvar y
  let cP: class P
  let cE: class E
  let cG: class G
  let cN: class N
  let cW: class W
  let vi: setvar i
  assume wwlksnredwwlkn.e: |- E = ( Edg ` G )

  disjoint E y
  disjoint G y
  disjoint N y
  disjoint W y
  disjoint P y
  disjoint E i
  disjoint G i
  disjoint N i
  disjoint W i
  assert |- ( ( N e. NN0 /\ W e. ( ( N + 1 ) WWalksN G ) ) -> ( ( W ` 0 ) = P <-> E. y e. ( N WWalksN G ) ( ( W substr <. 0 , ( N + 1 ) >. ) = y /\ ( y ` 0 ) = P /\ { ( lastS ` y ) , ( lastS ` W ) } e. E ) ) )

  proof
    cN
    cn0
    wcel
    #
    cW
    cN
    c1
    caddc
    co
    #
    cG
    cwwlksn
    co
    wcel
    #
    wa
    #
    cc0
    cW
    cfv
    #
    cP
    wceq
    #
    cW
    cc0
    @1
    cop
    csubstr
    co
    #
    vy
    cv
    #
    wceq
    #
    cc0
    @7
    cfv
    #
    cP
    wceq
    #
    @7
    clsw
    cfv
    cW
    clsw
    cfv
    cpr
    cE
    wcel
    #
    w3a
    #
    vy
    cN
    cG
    cwwlksn
    co
    #
    wrex
    #
    @8
    @11
    wa
    #
    vy
    @13
    wrex
    #
    @3
    @5
    @14
    wi
    @0
    @2
    @16
    vy
    cE
    cG
    cN
    cW
    wwlksnredwwlkn.e
    wwlksnredwwlkn
    imp
    @5
    @3
    @16
    @14
    @5
    @3
    @16
    @14
    wi
    @5
    @3
    wa
    #
    @15
    @12
    vy
    @13
    @17
    @7
    @13
    wcel
    #
    wa
    #
    @15
    @12
    @19
    @15
    wa
    @8
    @10
    @11
    @15
    @8
    @19
    @8
    @11
    simpl
    adantl
    @15
    @19
    @10
    @8
    @19
    @10
    wi
    @11
    @8
    @19
    @10
    @8
    @19
    wa
    #
    @9
    cc0
    @6
    cfv
    #
    @4
    cP
    @8
    @9
    @21
    wceq
    #
    @19
    @22
    @7
    @6
    cc0
    @7
    @6
    fveq1
    eqcoms
    adantr
    @20
    cW
    cG
    cvtx
    cfv
    #
    cword
    wcel
    #
    @1
    c1
    cW
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
    @21
    @4
    wceq
    #
    @19
    @28
    @8
    @17
    @28
    @18
    @3
    @28
    @5
    @2
    @0
    @28
    @2
    @24
    @25
    @1
    c1
    caddc
    co
    #
    wceq
    #
    vi
    cv
    #
    cW
    cfv
    @32
    c1
    caddc
    co
    cW
    cfv
    cpr
    cE
    wcel
    vi
    cc0
    @1
    cfzo
    co
    wral
    #
    w3a
    @0
    @28
    wi
    #
    vi
    cE
    cG
    @1
    @23
    cW
    @23
    eqid
    wwlksnredwwlkn.e
    wwlknp
    @24
    @31
    @34
    @33
    @24
    @31
    wa
    @0
    @27
    @24
    @31
    @0
    @27
    wi
    @24
    @0
    @27
    @31
    @1
    c1
    @30
    cfz
    co
    #
    wcel
    #
    @0
    @36
    @1
    cn
    wcel
    #
    @1
    @30
    cle
    wbr
    #
    cN
    nn0p1nn
    @0
    @1
    cn0
    wcel
    #
    @1
    cr
    wcel
    @38
    cN
    peano2nn0
    #
    @1
    nn0re
    @1
    lep1
    3syl
    @0
    @39
    @30
    cz
    wcel
    @36
    @37
    @38
    wa
    wb
    @40
    @39
    @30
    @1
    peano2nn0
    nn0zd
    @1
    @30
    fznn
    3syl
    mpbir2and
    @31
    @26
    @35
    @1
    @25
    @30
    c1
    cfz
    oveq2
    eleq2d
    syl5ibr
    adantl
    @24
    @31
    simpl
    jctild
    3adant3
    syl
    impcom
    #
    adantl
    adantr
    adantl
    @1
    @23
    cW
    swrd0fv0
    #
    syl
    @8
    @5
    @3
    @18
    simprll
    3eqtrd
    ex
    adantr
    impcom
    @15
    @11
    @19
    @8
    @11
    simpr
    adantl
    3jca
    ex
    reximdva
    ex
    com13
    mpcom
    @3
    @12
    @5
    vy
    @13
    @12
    @3
    @5
    @8
    @10
    @3
    @5
    wi
    @11
    @8
    @10
    wa
    #
    @3
    @5
    @43
    @3
    wa
    @4
    @21
    @9
    cP
    @3
    @4
    @21
    wceq
    @43
    @3
    @21
    @4
    @3
    @28
    @29
    @41
    @42
    syl
    eqcomd
    adantl
    @43
    @21
    @9
    wceq
    #
    @3
    @8
    @44
    @10
    cc0
    @6
    @7
    fveq1
    adantr
    adantr
    @43
    @10
    @3
    @8
    @10
    simpr
    adantr
    3eqtrd
    ex
    3adant3
    com12
    rexlimdvw
    impbid
end
