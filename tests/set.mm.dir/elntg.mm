include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "w3o.mm"
include "crab.mm"
include "cmpt2.mm"
include "ceeng.mm"
include "clng.mm"
include "co.mm"
include "cvv.mm"
include "lngid.mm"
include "fvex.mm"
include "a1i.mm"
include "ccnv.mm"
include "wfun.mm"
include "c0.mm"
include "c1.mm"
include "c7.mm"
include "cdc.mm"
include "cstr.mm"
include "eengstr.mm"
include "cle.mm"
include "w3a.mm"
include "cdm.mm"
include "cfz.mm"
include "wss.mm"
include "isstruct.mm"
include "simp2bi.mm"
include "syl.mm"
include "wceq.mm"
include "structcnvcnv.mm"
include "funeqd.mm"
include "mpbird.mm"
include "cnx.mm"
include "cbs.mm"
include "cds.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "cpr.mm"
include "citv.mm"
include "cun.mm"
include "opex.mm"
include "prid2.mm"
include "elun2.mm"
include "ax-mp.mm"
include "eengv.mm"
include "syl5eleqr.mm"
include "difexg.mm"
include "mpt2ex.mm"
include "strfv2d.mm"
include "eengbas.mm"
include "syl6eqr.mm"
include "difeq1d.mm"
include "adantr.mm"
include "wa.mm"
include "simpll.mm"
include "simplrl.mm"
include "eleqtrd.mm"
include "simplrr.mm"
include "eldifad.mm"
include "simpr.mm"
include "ebtwntg.mm"
include "3orbi123d.mm"
include "rabeqbidva.mm"
include "mpt2eq123dva.mm"
include "eqtr3d.mm"

theorem elntg
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cI: class I
  let cN: class N
  let vi: setvar i
  assume elntg.1: |- P = ( Base ` ( EEG ` N ) )
  assume elntg.2: |- I = ( Itv ` ( EEG ` N ) )

  disjoint x y
  disjoint x z
  disjoint N x
  disjoint y z
  disjoint N y
  disjoint N z
  disjoint P z
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint N i
  assert |- ( N e. NN -> ( LineG ` ( EEG ` N ) ) = ( x e. P , y e. ( P \ { x } ) |-> { z e. P | ( z e. ( x I y ) \/ x e. ( z I y ) \/ y e. ( x I z ) ) } ) )

  proof
    cN
    cn
    wcel
    #
    vx
    vy
    cN
    cee
    cfv
    #
    @1
    vx
    cv
    #
    csn
    #
    cdif
    #
    vz
    cv
    #
    @2
    vy
    cv
    #
    cop
    cbtwn
    wbr
    #
    @2
    @5
    @6
    cop
    cbtwn
    wbr
    #
    @6
    @2
    @5
    cop
    cbtwn
    wbr
    #
    w3o
    #
    vz
    @1
    crab
    #
    cmpt2
    #
    cN
    ceeng
    cfv
    #
    clng
    cfv
    vx
    vy
    cP
    cP
    @3
    cdif
    #
    @5
    @2
    @6
    cI
    co
    wcel
    #
    @2
    @5
    @6
    cI
    co
    wcel
    #
    @6
    @2
    @5
    cI
    co
    wcel
    #
    w3o
    #
    vz
    cP
    crab
    #
    cmpt2
    @0
    @12
    @13
    clng
    cvv
    cvv
    lngid
    @13
    cvv
    wcel
    @0
    cN
    ceeng
    fvex
    a1i
    @0
    @13
    ccnv
    ccnv
    #
    wfun
    @13
    c0
    csn
    cdif
    #
    wfun
    #
    @0
    @13
    c1
    c1
    c7
    cdc
    #
    cop
    #
    cstr
    wbr
    #
    @22
    cN
    eengstr
    #
    @25
    c1
    cn
    wcel
    @23
    cn
    wcel
    c1
    @23
    cle
    wbr
    w3a
    @22
    @13
    cdm
    c1
    @23
    cfz
    co
    wss
    @13
    c1
    @23
    isstruct
    simp2bi
    syl
    @0
    @20
    @21
    @0
    @25
    @20
    @21
    wceq
    @26
    @13
    @24
    structcnvcnv
    syl
    funeqd
    mpbird
    @0
    cnx
    clng
    cfv
    #
    @12
    cop
    #
    cnx
    cbs
    cfv
    @1
    cop
    cnx
    cds
    cfv
    vx
    vy
    @1
    @1
    c1
    cN
    cfz
    co
    vi
    cv
    #
    @2
    cfv
    @29
    @6
    cfv
    cmin
    co
    c2
    cexp
    co
    vi
    csu
    cmpt2
    cop
    cpr
    #
    cnx
    citv
    cfv
    vx
    vy
    @1
    @1
    @7
    vz
    @1
    crab
    cmpt2
    cop
    #
    @28
    cpr
    #
    cun
    #
    @13
    @28
    @32
    wcel
    @28
    @33
    wcel
    @31
    @28
    @27
    @12
    opex
    prid2
    @28
    @32
    @30
    elun2
    ax-mp
    vx
    vy
    vz
    vi
    cN
    eengv
    syl5eleqr
    @12
    cvv
    wcel
    @0
    vx
    vy
    @1
    @4
    @11
    cN
    cee
    fvex
    #
    @1
    cvv
    wcel
    @4
    cvv
    wcel
    @34
    @1
    @3
    cvv
    difexg
    ax-mp
    mpt2ex
    a1i
    strfv2d
    @0
    vx
    vy
    @1
    @4
    @11
    cP
    @14
    @19
    @0
    @1
    @13
    cbs
    cfv
    cP
    cN
    eengbas
    elntg.1
    syl6eqr
    #
    @0
    @4
    @14
    wceq
    @2
    @1
    wcel
    #
    @0
    @1
    cP
    @3
    @35
    difeq1d
    adantr
    @0
    @36
    @6
    @4
    wcel
    #
    wa
    #
    wa
    #
    @10
    @18
    vz
    @1
    cP
    @0
    @1
    cP
    wceq
    #
    @38
    @35
    adantr
    @39
    @5
    @1
    wcel
    #
    wa
    #
    @7
    @15
    @8
    @16
    @9
    @17
    @42
    cP
    cI
    cN
    @2
    @6
    @5
    @0
    @38
    @41
    simpll
    #
    elntg.1
    elntg.2
    @42
    @2
    @1
    cP
    @0
    @36
    @37
    @41
    simplrl
    @42
    @0
    @40
    @43
    @35
    syl
    #
    eleqtrd
    #
    @42
    @6
    @1
    cP
    @42
    @6
    @1
    @3
    @0
    @36
    @37
    @41
    simplrr
    eldifad
    @44
    eleqtrd
    #
    @42
    @5
    @1
    cP
    @39
    @41
    simpr
    @44
    eleqtrd
    #
    ebtwntg
    @42
    cP
    cI
    cN
    @5
    @6
    @2
    @43
    elntg.1
    elntg.2
    @47
    @46
    @45
    ebtwntg
    @42
    cP
    cI
    cN
    @2
    @5
    @6
    @43
    elntg.1
    elntg.2
    @45
    @47
    @46
    ebtwntg
    3orbi123d
    rabeqbidva
    mpt2eq123dva
    eqtr3d
end
