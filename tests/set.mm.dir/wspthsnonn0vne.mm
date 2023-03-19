include "cwwspthsnon.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "wex.mm"
include "wi.mm"
include "n0.mm"
include "cn0.mm"
include "cvv.mm"
include "wa.mm"
include "cvtx.mm"
include "cfv.mm"
include "cwwlksnon.mm"
include "cspthson.mm"
include "wbr.mm"
include "w3a.mm"
include "eqid.mm"
include "wspthnonp.mm"
include "cwwlksn.mm"
include "cc0.mm"
include "wceq.mm"
include "wwlknon.mm"
include "cwwlks.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "iswwlksn.mm"
include "cmin.mm"
include "cspths.mm"
include "cpths.mm"
include "spthonisspth.mm"
include "spthispth.mm"
include "cwlks.mm"
include "pthiswlk.mm"
include "wlklenvm1.mm"
include "syl.mm"
include "3syl.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "simpr.mm"
include "cc.mm"
include "nncn.mm"
include "pncan1.mm"
include "adantr.mm"
include "eqtrd.mm"
include "nnne0.mm"
include "eqnetrd.mm"
include "spthonepeq.mm"
include "necon3bid.mm"
include "syl5ibrcom.mm"
include "expcom.mm"
include "com23.mm"
include "syl6bi.mm"
include "com13.mm"
include "mpd.mm"
include "exlimiv.mm"
include "com12.mm"
include "adantl.mm"
include "3ad2ant1.mm"
include "syl5bi.mm"
include "impd.mm"
include "3impia.mm"
include "sylbi.mm"
include "impcom.mm"

theorem wspthsnonn0vne
  let cG: class G
  let cN: class N
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vp: setvar p


  assert |- ( ( N e. NN /\ ( X ( N WSPathsNOn G ) Y ) =/= (/) ) -> X =/= Y )

  proof
    cX
    cY
    cN
    cG
    cwwspthsnon
    co
    co
    #
    c0
    wne
    #
    cN
    cn
    wcel
    #
    cX
    cY
    wne
    #
    @1
    vp
    cv
    #
    @0
    wcel
    #
    vp
    wex
    @2
    @3
    wi
    #
    vp
    @0
    n0
    @5
    @6
    vp
    @5
    cN
    cn0
    wcel
    #
    cG
    cvv
    wcel
    #
    wa
    #
    cX
    cG
    cvtx
    cfv
    #
    wcel
    cY
    @10
    wcel
    wa
    #
    @4
    cX
    cY
    cN
    cG
    cwwlksnon
    co
    co
    wcel
    #
    vf
    cv
    #
    @4
    cX
    cY
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
    w3a
    @6
    cX
    cY
    vf
    cG
    cN
    @10
    @4
    @10
    eqid
    wspthnonp
    @9
    @11
    @16
    @6
    @9
    @11
    wa
    #
    @12
    @15
    @6
    @12
    @4
    cN
    cG
    cwwlksn
    co
    wcel
    #
    cc0
    @4
    cfv
    cX
    wceq
    #
    cN
    @4
    cfv
    cY
    wceq
    #
    w3a
    #
    @17
    @15
    @6
    wi
    #
    cX
    cY
    cG
    cN
    @4
    wwlknon
    @21
    @17
    @22
    @18
    @19
    @17
    @22
    wi
    @20
    @17
    @18
    @22
    @9
    @18
    @22
    wi
    #
    @11
    @7
    @23
    @8
    @7
    @18
    @4
    cG
    cwwlks
    cfv
    wcel
    #
    @4
    chash
    cfv
    #
    cN
    c1
    caddc
    co
    #
    wceq
    #
    wa
    @22
    cG
    cN
    @4
    iswwlksn
    @27
    @22
    @24
    @15
    @27
    @6
    @14
    @27
    @6
    wi
    #
    vf
    @14
    @13
    chash
    cfv
    #
    @25
    c1
    cmin
    co
    #
    wceq
    #
    @28
    @14
    @13
    @4
    cG
    cspths
    cfv
    wbr
    @13
    @4
    cG
    cpths
    cfv
    wbr
    #
    @31
    cX
    cY
    @4
    @13
    cG
    spthonisspth
    @4
    @13
    cG
    spthispth
    @32
    @13
    @4
    cG
    cwlks
    cfv
    wbr
    @31
    @4
    @13
    cG
    pthiswlk
    @4
    @13
    cG
    wlklenvm1
    syl
    3syl
    @27
    @31
    @14
    @6
    @27
    @31
    @29
    @26
    c1
    cmin
    co
    #
    wceq
    #
    @14
    @6
    wi
    @27
    @30
    @33
    @29
    @25
    @26
    c1
    cmin
    oveq1
    eqeq2d
    @34
    @2
    @14
    @3
    @2
    @34
    @14
    @3
    wi
    @2
    @34
    wa
    #
    @3
    @14
    @29
    cc0
    wne
    @35
    @29
    cN
    cc0
    @35
    @29
    @33
    cN
    @2
    @34
    simpr
    @2
    @33
    cN
    wceq
    #
    @34
    @2
    cN
    cc
    wcel
    @36
    cN
    nncn
    cN
    pncan1
    syl
    adantr
    eqtrd
    @2
    cN
    cc0
    wne
    @34
    cN
    nnne0
    adantr
    eqnetrd
    @14
    cX
    cY
    @29
    cc0
    cX
    cY
    @4
    @13
    cG
    spthonepeq
    necon3bid
    syl5ibrcom
    expcom
    com23
    syl6bi
    com13
    mpd
    exlimiv
    com12
    adantl
    syl6bi
    adantr
    adantr
    com12
    3ad2ant1
    com12
    syl5bi
    impd
    3impia
    syl
    exlimiv
    sylbi
    impcom
end
