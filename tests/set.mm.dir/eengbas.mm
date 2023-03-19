include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "ceeng.mm"
include "cbs.mm"
include "cvv.mm"
include "baseid.mm"
include "fvexd.mm"
include "ccnv.mm"
include "wfun.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "c1.mm"
include "c7.mm"
include "cdc.mm"
include "cop.mm"
include "cstr.mm"
include "wbr.mm"
include "eengstr.mm"
include "cle.mm"
include "w3a.mm"
include "cdm.mm"
include "cfz.mm"
include "co.mm"
include "wss.mm"
include "isstruct.mm"
include "simp2bi.mm"
include "syl.mm"
include "wceq.mm"
include "structcnvcnv.mm"
include "funeqd.mm"
include "mpbird.mm"
include "cnx.mm"
include "cds.mm"
include "cv.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "cmpt2.mm"
include "cpr.mm"
include "citv.mm"
include "cbtwn.mm"
include "crab.mm"
include "clng.mm"
include "w3o.mm"
include "cun.mm"
include "opex.mm"
include "prid1.mm"
include "elun1.mm"
include "ax-mp.mm"
include "eengv.mm"
include "syl5eleqr.mm"
include "strfv2d.mm"

theorem eengbas
  let cN: class N
  let vi: setvar i
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( N e. NN -> ( EE ` N ) = ( Base ` ( EEG ` N ) ) )

  proof
    cN
    cn
    wcel
    #
    cN
    cee
    cfv
    #
    cN
    ceeng
    cfv
    #
    cbs
    cvv
    cvv
    baseid
    @0
    cN
    ceeng
    fvexd
    @0
    @2
    ccnv
    ccnv
    #
    wfun
    @2
    c0
    csn
    cdif
    #
    wfun
    #
    @0
    @2
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
    @5
    cN
    eengstr
    #
    @8
    c1
    cn
    wcel
    @6
    cn
    wcel
    c1
    @6
    cle
    wbr
    w3a
    @5
    @2
    cdm
    c1
    @6
    cfz
    co
    wss
    @2
    c1
    @6
    isstruct
    simp2bi
    syl
    @0
    @3
    @4
    @0
    @8
    @3
    @4
    wceq
    @9
    @2
    @7
    structcnvcnv
    syl
    funeqd
    mpbird
    @0
    cnx
    cbs
    cfv
    #
    @1
    cop
    #
    @11
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
    vx
    cv
    #
    cfv
    @12
    vy
    cv
    #
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
    #
    cpr
    #
    cnx
    citv
    cfv
    vx
    vy
    @1
    @1
    vz
    cv
    #
    @13
    @14
    cop
    cbtwn
    wbr
    #
    vz
    @1
    crab
    cmpt2
    cop
    cnx
    clng
    cfv
    vx
    vy
    @1
    @1
    @13
    csn
    cdif
    @18
    @13
    @17
    @14
    cop
    cbtwn
    wbr
    @14
    @13
    @17
    cop
    cbtwn
    wbr
    w3o
    vz
    @1
    crab
    cmpt2
    cop
    cpr
    #
    cun
    #
    @2
    @11
    @16
    wcel
    @11
    @20
    wcel
    @11
    @15
    @10
    @1
    opex
    prid1
    @11
    @16
    @19
    elun1
    ax-mp
    vx
    vy
    vz
    vi
    cN
    eengv
    syl5eleqr
    @0
    cN
    cee
    fvexd
    strfv2d
end
