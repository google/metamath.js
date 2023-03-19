include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cwwspthsn.mm"
include "co.mm"
include "cwwlksn.mm"
include "cv.mm"
include "cspths.mm"
include "cfv.mm"
include "wbr.mm"
include "wex.mm"
include "cwwlksnon.mm"
include "wrex.mm"
include "cwwspthsnon.mm"
include "wb.mm"
include "iswspthn.mm"
include "a1i.mm"
include "wwlksnwwlksnonOLD.mm"
include "anbi1d.mm"
include "r19.41vv.mm"
include "syl6bbr.mm"
include "cspthson.mm"
include "cc0.mm"
include "wceq.mm"
include "chash.mm"
include "w3a.mm"
include "3anass.mm"
include "cvv.mm"
include "simpr.mm"
include "vex.mm"
include "jctl.mm"
include "isspthonpth.mm"
include "syl2an.mm"
include "cwlks.mm"
include "c1.mm"
include "cmin.mm"
include "wi.mm"
include "spthiswlk.mm"
include "wlklenvm1.mm"
include "wwlknonOLD.mm"
include "adantl.mm"
include "simpl2.mm"
include "cvtx.mm"
include "cword.mm"
include "caddc.mm"
include "wwlknbp2OLD.mm"
include "oveq1.mm"
include "cc.mm"
include "nn0cn.mm"
include "pncan1.mm"
include "syl.mm"
include "adantr.mm"
include "sylan9eq.mm"
include "ex.mm"
include "3ad2ant1.mm"
include "imp.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "simpl3.mm"
include "jca.mm"
include "exp32.mm"
include "com12.mm"
include "sylbid.mm"
include "3syl.mm"
include "pm4.71d.mm"
include "3bitr4rd.mm"
include "exbidv.mm"
include "pm5.32da.mm"
include "wspthnonOLDOLD.mm"
include "bitr4d.mm"
include "2rexbidva.mm"
include "3bitrd.mm"

theorem wspthsnwspthsnonOLD
  let cU: class U
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
  disjoint U a
  disjoint U b
  disjoint G f
  disjoint a f
  disjoint b f
  disjoint N f
  disjoint V f
  disjoint W f
  disjoint U f
  assert |- ( ( N e. NN0 /\ G e. U ) -> ( W e. ( N WSPathsN G ) <-> E. a e. V E. b e. V W e. ( a ( N WSPathsNOn G ) b ) ) )

  proof
    cN
    cn0
    wcel
    #
    cG
    cU
    wcel
    #
    wa
    #
    cW
    cN
    cG
    cwwspthsn
    co
    wcel
    #
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
    @7
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
    @9
    @10
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
    @3
    @8
    wb
    @2
    vf
    cG
    cN
    cW
    iswspthn
    a1i
    @2
    @8
    @12
    vb
    cV
    wrex
    va
    cV
    wrex
    #
    @7
    wa
    @14
    @2
    @4
    @16
    @7
    cU
    cG
    cN
    cV
    cW
    va
    vb
    wwlksnwwlksnon.v
    wwlksnwwlksnonOLD
    anbi1d
    @12
    @7
    va
    vb
    cV
    cV
    r19.41vv
    syl6bbr
    @2
    @13
    @15
    va
    vb
    cV
    cV
    @2
    @9
    cV
    wcel
    @10
    cV
    wcel
    wa
    #
    wa
    #
    @13
    @12
    @5
    cW
    @9
    @10
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
    #
    @15
    @18
    @12
    @7
    @20
    @18
    @12
    wa
    #
    @6
    @19
    vf
    @22
    @6
    cc0
    cW
    cfv
    @9
    wceq
    #
    @5
    chash
    cfv
    #
    cW
    cfv
    #
    @10
    wceq
    #
    w3a
    #
    @6
    @23
    @26
    wa
    #
    wa
    #
    @19
    @6
    @27
    @29
    wb
    @22
    @6
    @23
    @26
    3anass
    a1i
    @18
    @17
    @5
    cvv
    wcel
    #
    @12
    wa
    @19
    @27
    wb
    @12
    @2
    @17
    simpr
    @12
    @30
    vf
    vex
    jctl
    @9
    @10
    cW
    @5
    cG
    cV
    cvv
    @11
    wwlksnwwlksnon.v
    isspthonpth
    syl2an
    @22
    @6
    @28
    @6
    @22
    @28
    @6
    @5
    cW
    cG
    cwlks
    cfv
    wbr
    @24
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
    @22
    @28
    wi
    cW
    @5
    cG
    spthiswlk
    cW
    @5
    cG
    wlklenvm1
    @22
    @33
    @28
    @18
    @12
    @33
    @28
    wi
    #
    @18
    @12
    @4
    @23
    cN
    cW
    cfv
    #
    @10
    wceq
    #
    w3a
    #
    @34
    @17
    @12
    @37
    wb
    @2
    @9
    @10
    cG
    cN
    cV
    cW
    wwlksnwwlksnon.v
    wwlknonOLD
    adantl
    @2
    @37
    @34
    wi
    #
    @17
    @0
    @38
    @1
    @37
    @0
    @34
    @37
    @0
    @33
    @28
    @37
    @0
    @33
    wa
    #
    wa
    #
    @23
    @26
    @4
    @23
    @36
    @39
    simpl2
    @40
    @25
    @35
    @10
    @40
    @24
    cN
    cW
    @40
    @24
    @32
    cN
    @39
    @33
    @37
    @0
    @33
    simpr
    adantl
    @37
    @39
    @32
    cN
    wceq
    #
    @4
    @23
    @39
    @41
    wi
    #
    @36
    @4
    cW
    cG
    cvtx
    cfv
    cword
    wcel
    #
    @31
    cN
    c1
    caddc
    co
    #
    wceq
    #
    wa
    #
    @42
    cG
    cN
    cW
    wwlknbp2OLD
    @46
    @39
    @41
    @46
    @39
    @32
    @44
    c1
    cmin
    co
    #
    cN
    @45
    @32
    @47
    wceq
    @43
    @31
    @44
    c1
    cmin
    oveq1
    adantl
    @0
    @47
    cN
    wceq
    #
    @33
    @0
    cN
    cc
    wcel
    @48
    cN
    nn0cn
    cN
    pncan1
    syl
    adantr
    sylan9eq
    ex
    syl
    3ad2ant1
    imp
    eqtrd
    fveq2d
    @4
    @23
    @36
    @39
    simpl3
    eqtrd
    jca
    exp32
    com12
    adantr
    adantr
    sylbid
    imp
    com12
    3syl
    com12
    pm4.71d
    3bitr4rd
    exbidv
    pm5.32da
    @17
    @15
    @21
    wb
    @2
    @9
    @10
    vf
    cG
    cN
    cV
    cW
    wwlksnwwlksnon.v
    wspthnonOLDOLD
    adantl
    bitr4d
    2rexbidva
    3bitrd
end
