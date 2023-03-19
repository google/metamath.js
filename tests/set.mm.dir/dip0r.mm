include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cpv.mm"
include "cfv.mm"
include "cnmcv.mm"
include "c2.mm"
include "cexp.mm"
include "c1.mm"
include "cneg.mm"
include "cns.mm"
include "cmin.mm"
include "ci.mm"
include "cmul.mm"
include "caddc.mm"
include "c4.mm"
include "cdiv.mm"
include "cc0.mm"
include "wceq.mm"
include "nvzcl.mm"
include "adantr.mm"
include "eqid.mm"
include "ipval2.mm"
include "mpd3an3.mm"
include "cc.mm"
include "neg1cn.mm"
include "nvsz.mm"
include "mpan2.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "cr.mm"
include "ipval2lem3.mm"
include "recnd.mm"
include "subidd.mm"
include "eqtrd.mm"
include "negicn.mm"
include "ax-icn.mm"
include "eqtr4d.mm"
include "w3a.mm"
include "ipval2lem4.mm"
include "oveq12d.mm"
include "it0e0.mm"
include "oveq2i.mm"
include "00id.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "4cn.mm"
include "4ne0.mm"
include "div0i.mm"

theorem dip0r
  let cA: class A
  let cP: class P
  let cU: class U
  let cX: class X
  let cZ: class Z
  assume dip0r.1: |- X = ( BaseSet ` U )
  assume dip0r.5: |- Z = ( 0vec ` U )
  assume dip0r.7: |- P = ( .iOLD ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X ) -> ( A P Z ) = 0 )

  proof
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cA
    cZ
    cP
    co
    #
    cA
    cZ
    cU
    cpv
    cfv
    #
    co
    #
    cU
    cnmcv
    cfv
    #
    cfv
    #
    c2
    cexp
    co
    #
    cA
    c1
    cneg
    #
    cZ
    cU
    cns
    cfv
    #
    co
    #
    @4
    co
    #
    @6
    cfv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    ci
    cA
    ci
    cZ
    @10
    co
    #
    @4
    co
    #
    @6
    cfv
    #
    c2
    cexp
    co
    #
    cA
    ci
    cneg
    #
    cZ
    @10
    co
    #
    @4
    co
    #
    @6
    cfv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    c4
    cdiv
    co
    #
    cc0
    @0
    @1
    cZ
    cX
    wcel
    #
    @3
    @28
    wceq
    @0
    @29
    @1
    cU
    cX
    cZ
    dip0r.1
    dip0r.5
    nvzcl
    adantr
    #
    cA
    cZ
    cP
    @10
    cU
    @4
    @6
    cX
    dip0r.1
    @4
    eqid
    #
    @10
    eqid
    #
    @6
    eqid
    #
    dip0r.7
    ipval2
    mpd3an3
    @2
    @28
    cc0
    c4
    cdiv
    co
    cc0
    @2
    @27
    cc0
    c4
    cdiv
    @2
    @27
    cc0
    ci
    cc0
    cmul
    co
    #
    caddc
    co
    #
    cc0
    @2
    @15
    cc0
    @26
    @34
    caddc
    @2
    @15
    @8
    @8
    cmin
    co
    cc0
    @2
    @14
    @8
    @8
    cmin
    @2
    @13
    @7
    c2
    cexp
    @2
    @12
    @5
    @6
    @2
    @11
    cZ
    cA
    @4
    @0
    @11
    cZ
    wceq
    #
    @1
    @0
    @9
    cc
    wcel
    @36
    neg1cn
    @9
    @10
    cU
    cZ
    @32
    dip0r.5
    nvsz
    mpan2
    adantr
    oveq2d
    fveq2d
    oveq1d
    oveq2d
    @2
    @8
    @2
    @8
    @0
    @1
    @29
    @8
    cr
    wcel
    @30
    cA
    cZ
    cP
    @10
    cU
    @4
    @6
    cX
    dip0r.1
    @31
    @32
    @33
    dip0r.7
    ipval2lem3
    mpd3an3
    recnd
    subidd
    eqtrd
    @2
    @25
    cc0
    ci
    cmul
    @2
    @25
    @19
    @19
    cmin
    co
    cc0
    @2
    @24
    @19
    @19
    cmin
    @2
    @23
    @18
    c2
    cexp
    @2
    @22
    @17
    @6
    @2
    @21
    @16
    cA
    @4
    @0
    @21
    @16
    wceq
    @1
    @0
    @21
    cZ
    @16
    @0
    @20
    cc
    wcel
    @21
    cZ
    wceq
    negicn
    @20
    @10
    cU
    cZ
    @32
    dip0r.5
    nvsz
    mpan2
    @0
    ci
    cc
    wcel
    #
    @16
    cZ
    wceq
    ax-icn
    ci
    @10
    cU
    cZ
    @32
    dip0r.5
    nvsz
    mpan2
    eqtr4d
    adantr
    oveq2d
    fveq2d
    oveq1d
    oveq2d
    @2
    @19
    @0
    @1
    @29
    @19
    cc
    wcel
    #
    @30
    @0
    @1
    @29
    w3a
    @37
    @38
    ax-icn
    cA
    cZ
    ci
    cP
    @10
    cU
    @4
    @6
    cX
    dip0r.1
    @31
    @32
    @33
    dip0r.7
    ipval2lem4
    mpan2
    mpd3an3
    subidd
    eqtrd
    oveq2d
    oveq12d
    @35
    cc0
    cc0
    caddc
    co
    cc0
    @34
    cc0
    cc0
    caddc
    it0e0
    oveq2i
    00id
    eqtri
    syl6eq
    oveq1d
    c4
    4cn
    4ne0
    div0i
    syl6eq
    eqtrd
end
