include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cpc.mm"
include "co.mm"
include "cv.mm"
include "cdiv.mm"
include "wceq.mm"
include "cexp.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn0.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cmin.mm"
include "cn.mm"
include "wrex.mm"
include "cio.mm"
include "cq.mm"
include "zq.mm"
include "eqid.mm"
include "pcval.mm"
include "sylanr1.mm"
include "c1.mm"
include "simprl.mm"
include "zcnd.mm"
include "div1d.mm"
include "eqcomd.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "prmuz2.mm"
include "pcpre1.mm"
include "sylancl.mm"
include "adantr.mm"
include "oveq2d.mm"
include "pcprecl.mm"
include "sylan.mm"
include "simpld.mm"
include "nn0cnd.mm"
include "subid1d.mm"
include "eqtr2d.mm"
include "1nn.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "breq2.mm"
include "rabbidv.mm"
include "supeq1d.mm"
include "syl6eqr.mm"
include "oveq1d.mm"
include "anbi12d.mm"
include "oveq2.mm"
include "rspc2ev.mm"
include "mp3an2.mm"
include "syl12anc.mm"
include "cvv.mm"
include "weu.mm"
include "wb.mm"
include "ltso.mm"
include "supex.mm"
include "eqeltri.mm"
include "pceu.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "2rexbidv.mm"
include "iota2.mm"
include "sylancr.mm"
include "mpbid.mm"
include "eqtrd.mm"

theorem pczpre
  let cP: class P
  let cS: class S
  let vn: setvar n
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume pczpre.1: |- S = sup ( { n e. NN0 | ( P ^ n ) || N } , RR , < )

  disjoint N n
  disjoint P n
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint N x
  disjoint y z
  disjoint N y
  disjoint N z
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint S x
  disjoint S y
  disjoint S z
  assert |- ( ( P e. Prime /\ ( N e. ZZ /\ N =/= 0 ) ) -> ( P pCnt N ) = S )

  proof
    cP
    cprime
    wcel
    #
    cN
    cz
    wcel
    #
    cN
    cc0
    wne
    #
    wa
    #
    wa
    #
    cP
    cN
    cpc
    co
    #
    cN
    vx
    cv
    #
    vy
    cv
    #
    cdiv
    co
    #
    wceq
    #
    vz
    cv
    #
    cP
    vn
    cv
    cexp
    co
    #
    @6
    cdvds
    wbr
    #
    vn
    cn0
    crab
    #
    cr
    clt
    csup
    #
    @11
    @7
    cdvds
    wbr
    #
    vn
    cn0
    crab
    #
    cr
    clt
    csup
    #
    cmin
    co
    #
    wceq
    #
    wa
    #
    vy
    cn
    wrex
    vx
    cz
    wrex
    #
    vz
    cio
    #
    cS
    @1
    @0
    cN
    cq
    wcel
    #
    @2
    @5
    @22
    wceq
    cN
    zq
    #
    vx
    vy
    vz
    cP
    @14
    @17
    vn
    cN
    @14
    eqid
    #
    @17
    eqid
    #
    pcval
    sylanr1
    @4
    @9
    cS
    @18
    wceq
    #
    wa
    #
    vy
    cn
    wrex
    vx
    cz
    wrex
    #
    @22
    cS
    wceq
    #
    @4
    @1
    cN
    cN
    c1
    cdiv
    co
    #
    wceq
    #
    cS
    cS
    @11
    c1
    cdvds
    wbr
    #
    vn
    cn0
    crab
    #
    cr
    clt
    csup
    #
    cmin
    co
    #
    wceq
    #
    @29
    @0
    @1
    @2
    simprl
    #
    @4
    @31
    cN
    @4
    cN
    @4
    cN
    @38
    zcnd
    div1d
    eqcomd
    @4
    @36
    cS
    cc0
    cmin
    co
    cS
    @4
    @35
    cc0
    cS
    cmin
    @0
    @35
    cc0
    wceq
    #
    @3
    @0
    cP
    c2
    cuz
    cfv
    wcel
    #
    c1
    c1
    wceq
    @39
    cP
    prmuz2
    #
    c1
    eqid
    @34
    cP
    @35
    vn
    c1
    @34
    eqid
    @35
    eqid
    pcpre1
    sylancl
    adantr
    oveq2d
    @4
    cS
    @4
    cS
    @4
    cS
    cn0
    wcel
    #
    cP
    cS
    cexp
    co
    cN
    cdvds
    wbr
    #
    @0
    @40
    @3
    @42
    @43
    wa
    @41
    @11
    cN
    cdvds
    wbr
    #
    vn
    cn0
    crab
    #
    cP
    cS
    vn
    cN
    @45
    eqid
    pczpre.1
    pcprecl
    sylan
    simpld
    nn0cnd
    subid1d
    eqtr2d
    @1
    c1
    cn
    wcel
    @32
    @37
    wa
    #
    @29
    1nn
    @28
    @46
    cN
    cN
    @7
    cdiv
    co
    #
    wceq
    #
    cS
    cS
    @17
    cmin
    co
    #
    wceq
    #
    wa
    vx
    vy
    cN
    c1
    cz
    cn
    @6
    cN
    wceq
    #
    @9
    @48
    @27
    @50
    @51
    @8
    @47
    cN
    @6
    cN
    @7
    cdiv
    oveq1
    eqeq2d
    @51
    @18
    @49
    cS
    @51
    @14
    cS
    @17
    cmin
    @51
    @14
    @45
    cr
    clt
    csup
    #
    cS
    @51
    cr
    @13
    @45
    clt
    @51
    @12
    @44
    vn
    cn0
    @6
    cN
    @11
    cdvds
    breq2
    rabbidv
    supeq1d
    pczpre.1
    syl6eqr
    oveq1d
    eqeq2d
    anbi12d
    @7
    c1
    wceq
    #
    @48
    @32
    @50
    @37
    @53
    @47
    @31
    cN
    @7
    c1
    cN
    cdiv
    oveq2
    eqeq2d
    @53
    @49
    @36
    cS
    @53
    @17
    @35
    cS
    cmin
    @53
    cr
    @16
    @34
    clt
    @53
    @15
    @33
    vn
    cn0
    @7
    c1
    @11
    cdvds
    breq2
    rabbidv
    supeq1d
    oveq2d
    eqeq2d
    anbi12d
    rspc2ev
    mp3an2
    syl12anc
    @4
    cS
    cvv
    wcel
    @21
    vz
    weu
    #
    @29
    @30
    wb
    cS
    @52
    cvv
    pczpre.1
    cr
    @45
    clt
    ltso
    supex
    eqeltri
    @1
    @0
    @23
    @2
    @54
    @24
    vx
    vy
    vz
    cP
    @14
    @17
    vn
    cN
    @25
    @26
    pceu
    sylanr1
    @21
    @29
    vz
    cS
    cvv
    @10
    cS
    wceq
    #
    @20
    @28
    vx
    vy
    cz
    cn
    @55
    @19
    @27
    @9
    @10
    cS
    @18
    eqeq1
    anbi2d
    2rexbidv
    iota2
    sylancr
    mpbid
    eqtrd
end
