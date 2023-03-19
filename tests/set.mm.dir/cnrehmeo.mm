include "ctx.mm"
include "co.mm"
include "chmeo.mm"
include "wcel.mm"
include "wtru.mm"
include "ccn.mm"
include "ccnv.mm"
include "cr.mm"
include "cv.mm"
include "ci.mm"
include "cmul.mm"
include "caddc.mm"
include "cmpt2.mm"
include "ctopon.mm"
include "cfv.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "retopon.mm"
include "eqeltri.mm"
include "a1i.mm"
include "crest.mm"
include "ctop.mm"
include "wss.mm"
include "cnfldtop.mm"
include "cnrest2r.mm"
include "mp1i.mm"
include "cnmpt1st.mm"
include "tgioo2.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "syl6eleq.mm"
include "sseldd.mm"
include "cc.mm"
include "cnfldtopon.mm"
include "ax-icn.mm"
include "cnmpt2c.mm"
include "cnmpt2nd.mm"
include "mulcn.mm"
include "cnmpt22f.mm"
include "addcn.mm"
include "syl5eqel.mm"
include "cre.mm"
include "cim.mm"
include "cop.mm"
include "cmpt.mm"
include "cnrecnv.mm"
include "wf.mm"
include "ref.mm"
include "feqmptd.mm"
include "ccncf.mm"
include "recncf.mm"
include "wceq.mm"
include "ssid.mm"
include "ax-resscn.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cncfcn.mm"
include "mp2an.mm"
include "eleqtri.mm"
include "syl6eqelr.mm"
include "imf.mm"
include "imcncf.mm"
include "cnmpt1t.mm"
include "ishmeo.mm"
include "sylanbrc.mm"
include "trud.mm"

theorem cnrehmeo
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cJ: class J
  let cK: class K
  let vz: setvar z
  assume cnrehmeo.1: |- F = ( x e. RR , y e. RR |-> ( x + ( _i x. y ) ) )
  assume cnrehmeo.2: |- J = ( topGen ` ran (,) )
  assume cnrehmeo.3: |- K = ( TopOpen ` CCfld )

  disjoint x y
  disjoint K x
  disjoint K y
  disjoint F z
  disjoint J z
  disjoint x z
  disjoint y z
  disjoint K z
  assert |- F e. ( ( J tX J ) Homeo K )

  proof
    cF
    cJ
    cJ
    ctx
    co
    #
    cK
    chmeo
    co
    wcel
    #
    wtru
    cF
    @0
    cK
    ccn
    co
    #
    wcel
    cF
    ccnv
    #
    cK
    @0
    ccn
    co
    #
    wcel
    @1
    wtru
    cF
    vx
    vy
    cr
    cr
    vx
    cv
    #
    ci
    vy
    cv
    #
    cmul
    co
    #
    caddc
    co
    cmpt2
    @2
    cnrehmeo.1
    wtru
    vx
    vy
    @5
    @7
    caddc
    cJ
    cJ
    cK
    cK
    cK
    cr
    cr
    cJ
    cr
    ctopon
    cfv
    #
    wcel
    wtru
    cJ
    cioo
    crn
    ctg
    cfv
    #
    @8
    cnrehmeo.2
    retopon
    eqeltri
    a1i
    #
    @10
    wtru
    @0
    cK
    cr
    crest
    co
    #
    ccn
    co
    #
    @2
    vx
    vy
    cr
    cr
    @5
    cmpt2
    #
    cK
    ctop
    wcel
    @12
    @2
    wss
    wtru
    cK
    cnrehmeo.3
    cnfldtop
    cr
    @0
    cK
    cnrest2r
    mp1i
    #
    wtru
    @13
    @0
    cJ
    ccn
    co
    #
    @12
    wtru
    vx
    vy
    cJ
    cJ
    cr
    cr
    @10
    @10
    cnmpt1st
    cJ
    @11
    @0
    ccn
    cJ
    @9
    @11
    cnrehmeo.2
    cK
    cnrehmeo.3
    tgioo2
    eqtri
    #
    oveq2i
    #
    syl6eleq
    sseldd
    wtru
    vx
    vy
    ci
    @6
    cmul
    cJ
    cJ
    cK
    cK
    cK
    cr
    cr
    @10
    @10
    wtru
    vx
    vy
    ci
    cJ
    cJ
    cK
    cr
    cr
    cc
    @10
    @10
    cK
    cc
    ctopon
    cfv
    #
    wcel
    #
    wtru
    cK
    cnrehmeo.3
    cnfldtopon
    #
    a1i
    #
    ci
    cc
    wcel
    wtru
    ax-icn
    a1i
    cnmpt2c
    wtru
    @12
    @2
    vx
    vy
    cr
    cr
    @6
    cmpt2
    #
    @14
    wtru
    @22
    @15
    @12
    wtru
    vx
    vy
    cJ
    cJ
    cr
    cr
    @10
    @10
    cnmpt2nd
    @17
    syl6eleq
    sseldd
    cmul
    cK
    cK
    ctx
    co
    cK
    ccn
    co
    #
    wcel
    wtru
    cK
    cnrehmeo.3
    mulcn
    a1i
    cnmpt22f
    caddc
    @23
    wcel
    wtru
    cK
    cnrehmeo.3
    addcn
    a1i
    cnmpt22f
    syl5eqel
    wtru
    @3
    vz
    cc
    vz
    cv
    #
    cre
    cfv
    #
    @24
    cim
    cfv
    #
    cop
    cmpt
    @4
    vx
    vy
    vz
    cF
    cnrehmeo.1
    cnrecnv
    wtru
    vz
    @25
    @26
    cK
    cJ
    cJ
    cc
    @21
    wtru
    vz
    cc
    @25
    cmpt
    cre
    cK
    cJ
    ccn
    co
    #
    wtru
    vz
    cc
    cr
    cre
    cc
    cr
    cre
    wf
    wtru
    ref
    a1i
    feqmptd
    cre
    cc
    cr
    ccncf
    co
    #
    @27
    recncf
    cc
    cc
    wss
    cr
    cc
    wss
    @28
    @27
    wceq
    cc
    ssid
    ax-resscn
    cc
    cr
    cK
    cK
    cJ
    cnrehmeo.3
    cK
    cc
    crest
    co
    #
    cK
    @19
    @29
    cK
    wceq
    @20
    cK
    @18
    cc
    cc
    cK
    @20
    toponunii
    restid
    ax-mp
    eqcomi
    @16
    cncfcn
    mp2an
    #
    eleqtri
    syl6eqelr
    wtru
    vz
    cc
    @26
    cmpt
    cim
    @27
    wtru
    vz
    cc
    cr
    cim
    cc
    cr
    cim
    wf
    wtru
    imf
    a1i
    feqmptd
    cim
    @28
    @27
    imcncf
    @30
    eleqtri
    syl6eqelr
    cnmpt1t
    syl5eqel
    cF
    @0
    cK
    ishmeo
    sylanbrc
    trud
end
