include "wcel.mm"
include "cv.mm"
include "wne.mm"
include "wrex.mm"
include "c2.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "clt.mm"
include "w3o.mm"
include "wi.mm"
include "hashv01gt1.mm"
include "c0.mm"
include "hasheq0.mm"
include "rexeq.mm"
include "wn.mm"
include "rex0.mm"
include "pm2.21.mm"
include "mp1i.mm"
include "sylbid.mm"
include "syl6bi.mm"
include "com12.mm"
include "csn.mm"
include "wex.mm"
include "hash1snb.mm"
include "id.mm"
include "rexeqbidv.mm"
include "vex.mm"
include "weq.mm"
include "neeq1.mm"
include "rexbidv.mm"
include "rexsn.mm"
include "neeq2.mm"
include "bitri.mm"
include "syl6bb.mm"
include "equid.mm"
include "eqneqall.mm"
include "exlimiv.mm"
include "wa.mm"
include "cn0.mm"
include "cpnf.mm"
include "wo.mm"
include "hashnn0pnf.mm"
include "caddc.mm"
include "co.mm"
include "cz.mm"
include "1z.mm"
include "nn0z.mm"
include "zltp1le.mm"
include "biimpd.mm"
include "sylancr.mm"
include "df-2.mm"
include "breq1i.mm"
include "syl6ibr.mm"
include "cxr.mm"
include "2re.mm"
include "rexri.mm"
include "pnfge.mm"
include "breq2.mm"
include "mpbird.mm"
include "a1d.mm"
include "jaoi.mm"
include "syl.mm"
include "impcom.mm"
include "ex.mm"
include "3jaoi.mm"
include "mpcom.mm"
include "imp.mm"

theorem hashge2el2difr
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cV: class V
  let vz: setvar z

  disjoint x y
  disjoint D x
  disjoint D y
  disjoint V x
  disjoint V y
  disjoint x z
  disjoint y z
  disjoint D z
  assert |- ( ( D e. V /\ E. x e. D E. y e. D x =/= y ) -> 2 <_ ( # ` D ) )

  proof
    cD
    cV
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    vy
    cD
    wrex
    #
    vx
    cD
    wrex
    #
    c2
    cD
    chash
    cfv
    #
    cle
    wbr
    #
    @6
    cc0
    wceq
    #
    @6
    c1
    wceq
    #
    c1
    @6
    clt
    wbr
    #
    w3o
    @0
    @5
    @7
    wi
    #
    cD
    cV
    hashv01gt1
    @8
    @0
    @11
    wi
    @9
    @10
    @0
    @8
    @11
    @0
    @8
    cD
    c0
    wceq
    #
    @11
    cD
    cV
    hasheq0
    @12
    @5
    @4
    vx
    c0
    wrex
    #
    @7
    @4
    vx
    cD
    c0
    rexeq
    @13
    wn
    @13
    @7
    wi
    @12
    @4
    vx
    rex0
    @13
    @7
    pm2.21
    mp1i
    sylbid
    syl6bi
    com12
    @0
    @9
    @11
    @0
    @9
    cD
    vz
    cv
    #
    csn
    #
    wceq
    #
    vz
    wex
    @11
    cD
    cV
    vz
    hash1snb
    @16
    @11
    vz
    @16
    @5
    @14
    @14
    wne
    #
    @7
    @16
    @5
    @3
    vy
    @15
    wrex
    #
    vx
    @15
    wrex
    #
    @17
    @16
    @4
    @18
    vx
    cD
    @15
    @16
    id
    @3
    vy
    cD
    @15
    rexeq
    rexeqbidv
    @19
    @14
    @2
    wne
    #
    vy
    @15
    wrex
    #
    @17
    @18
    @21
    vx
    @14
    vz
    vex
    #
    vx
    vz
    weq
    @3
    @20
    vy
    @15
    @1
    @14
    @2
    neeq1
    rexbidv
    rexsn
    @20
    @17
    vy
    @14
    @22
    @2
    @14
    @14
    neeq2
    rexsn
    bitri
    syl6bb
    vz
    vz
    weq
    @17
    @7
    wi
    @16
    vz
    equid
    @7
    @14
    @14
    eqneqall
    mp1i
    sylbid
    exlimiv
    syl6bi
    com12
    @10
    @0
    @11
    @10
    @0
    wa
    @7
    @5
    @0
    @10
    @7
    @0
    @6
    cn0
    wcel
    #
    @6
    cpnf
    wceq
    #
    wo
    @10
    @7
    wi
    #
    cD
    cV
    hashnn0pnf
    @23
    @25
    @24
    @23
    @10
    c1
    c1
    caddc
    co
    #
    @6
    cle
    wbr
    #
    @7
    @23
    c1
    cz
    wcel
    #
    @6
    cz
    wcel
    #
    @10
    @27
    wi
    1z
    @6
    nn0z
    @28
    @29
    wa
    @10
    @27
    c1
    @6
    zltp1le
    biimpd
    sylancr
    c2
    @26
    @6
    cle
    df-2
    breq1i
    syl6ibr
    @24
    @7
    @10
    @24
    @7
    c2
    cpnf
    cle
    wbr
    #
    c2
    cxr
    wcel
    @30
    @24
    c2
    2re
    rexri
    c2
    pnfge
    mp1i
    @6
    cpnf
    c2
    cle
    breq2
    mpbird
    a1d
    jaoi
    syl
    impcom
    a1d
    ex
    3jaoi
    mpcom
    imp
end
