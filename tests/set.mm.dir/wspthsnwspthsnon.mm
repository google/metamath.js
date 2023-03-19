include "cwwspthsn.mm"
include "co.mm"
include "wcel.mm"
include "cwwlksn.mm"
include "cv.mm"
include "cspths.mm"
include "cfv.mm"
include "wbr.mm"
include "wex.mm"
include "wa.mm"
include "cwwlksnon.mm"
include "wrex.mm"
include "cwwspthsnon.mm"
include "iswspthn.mm"
include "wwlksnwwlksnon.mm"
include "anbi1i.mm"
include "r19.41vv.mm"
include "bitr4i.mm"
include "cspthson.mm"
include "cc0.mm"
include "wceq.mm"
include "chash.mm"
include "w3a.mm"
include "wb.mm"
include "3anass.mm"
include "a1i.mm"
include "cvv.mm"
include "vex.mm"
include "isspthonpth.mm"
include "mpanr1.mm"
include "cwlks.mm"
include "c1.mm"
include "cmin.mm"
include "wi.mm"
include "spthiswlk.mm"
include "wlklenvm1.mm"
include "wwlknon.mm"
include "simpl2.mm"
include "simpr.mm"
include "cn0.mm"
include "cvtx.mm"
include "cword.mm"
include "caddc.mm"
include "wwlknbp1.mm"
include "oveq1.mm"
include "3ad2ant3.mm"
include "cc.mm"
include "nn0cn.mm"
include "pncan1.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "eqtrd.mm"
include "adantr.mm"
include "fveq2d.mm"
include "simpl3.mm"
include "jca.mm"
include "ex.mm"
include "sylbi.mm"
include "adantl.mm"
include "com12.mm"
include "3syl.mm"
include "pm4.71d.mm"
include "3bitr4rd.mm"
include "exbidv.mm"
include "pm5.32da.mm"
include "wspthnon.mm"
include "syl6bbr.mm"
include "2rexbiia.mm"
include "3bitri.mm"

theorem wspthsnwspthsnon
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  assume wwlksnwwlksnon.v: |- V = ( Vtx ` G )

  disjoint G a
  disjoint G b
  disjoint a b
  disjoint N a
  disjoint N b
  disjoint V a
  disjoint V b
  disjoint W a
  disjoint W b
  disjoint G f
  disjoint a f
  disjoint b f
  disjoint N f
  disjoint V f
  disjoint W f
  assert |- ( W e. ( N WSPathsN G ) <-> E. a e. V E. b e. V W e. ( a ( N WSPathsNOn G ) b ) )

  proof
    cW
    cN
    cG
    cwwspthsn
    co
    wcel
    cW
    cN
    cG
    cwwlksn
    co
    wcel
    #
    vf
    cv
    #
    cW
    cG
    cspths
    cfv
    wbr
    #
    vf
    wex
    #
    wa
    #
    cW
    va
    cv
    #
    vb
    cv
    #
    cN
    cG
    cwwlksnon
    co
    co
    #
    wcel
    #
    @3
    wa
    #
    vb
    cV
    wrex
    va
    cV
    wrex
    #
    cW
    @5
    @6
    cN
    cG
    cwwspthsnon
    co
    co
    wcel
    #
    vb
    cV
    wrex
    va
    cV
    wrex
    vf
    cG
    cN
    cW
    iswspthn
    @4
    @8
    vb
    cV
    wrex
    va
    cV
    wrex
    #
    @3
    wa
    @10
    @0
    @12
    @3
    cG
    cN
    cV
    cW
    va
    vb
    wwlksnwwlksnon.v
    wwlksnwwlksnon
    anbi1i
    @8
    @3
    va
    vb
    cV
    cV
    r19.41vv
    bitr4i
    @9
    @11
    va
    vb
    cV
    cV
    @5
    cV
    wcel
    @6
    cV
    wcel
    wa
    #
    @9
    @8
    @1
    cW
    @5
    @6
    cG
    cspthson
    cfv
    co
    wbr
    #
    vf
    wex
    #
    wa
    @11
    @13
    @8
    @3
    @15
    @13
    @8
    wa
    #
    @2
    @14
    vf
    @16
    @2
    cc0
    cW
    cfv
    @5
    wceq
    #
    @1
    chash
    cfv
    #
    cW
    cfv
    #
    @6
    wceq
    #
    w3a
    #
    @2
    @17
    @20
    wa
    #
    wa
    #
    @14
    @2
    @21
    @23
    wb
    @16
    @2
    @17
    @20
    3anass
    a1i
    @13
    @1
    cvv
    wcel
    @8
    @14
    @21
    wb
    vf
    vex
    @5
    @6
    cW
    @1
    cG
    cV
    cvv
    @7
    wwlksnwwlksnon.v
    isspthonpth
    mpanr1
    @16
    @2
    @22
    @2
    @16
    @22
    @2
    @1
    cW
    cG
    cwlks
    cfv
    wbr
    @18
    cW
    chash
    cfv
    #
    c1
    cmin
    co
    #
    wceq
    #
    @16
    @22
    wi
    cW
    @1
    cG
    spthiswlk
    cW
    @1
    cG
    wlklenvm1
    @16
    @26
    @22
    @8
    @26
    @22
    wi
    #
    @13
    @8
    @0
    @17
    cN
    cW
    cfv
    #
    @6
    wceq
    #
    w3a
    #
    @27
    @5
    @6
    cG
    cN
    cW
    wwlknon
    @30
    @26
    @22
    @30
    @26
    wa
    #
    @17
    @20
    @0
    @17
    @29
    @26
    simpl2
    @31
    @19
    @28
    @6
    @31
    @18
    cN
    cW
    @31
    @18
    @25
    cN
    @30
    @26
    simpr
    @30
    @25
    cN
    wceq
    #
    @26
    @0
    @17
    @32
    @29
    @0
    cN
    cn0
    wcel
    #
    cW
    cG
    cvtx
    cfv
    cword
    wcel
    #
    @24
    cN
    c1
    caddc
    co
    #
    wceq
    #
    w3a
    #
    @32
    cG
    cN
    cW
    wwlknbp1
    @37
    @25
    @35
    c1
    cmin
    co
    #
    cN
    @36
    @33
    @25
    @38
    wceq
    @34
    @24
    @35
    c1
    cmin
    oveq1
    3ad2ant3
    @33
    @34
    @38
    cN
    wceq
    #
    @36
    @33
    cN
    cc
    wcel
    @39
    cN
    nn0cn
    cN
    pncan1
    syl
    3ad2ant1
    eqtrd
    syl
    3ad2ant1
    adantr
    eqtrd
    fveq2d
    @0
    @17
    @29
    @26
    simpl3
    eqtrd
    jca
    ex
    sylbi
    adantl
    com12
    3syl
    com12
    pm4.71d
    3bitr4rd
    exbidv
    pm5.32da
    @5
    @6
    vf
    cG
    cN
    cW
    wspthnon
    syl6bbr
    2rexbiia
    3bitri
end
