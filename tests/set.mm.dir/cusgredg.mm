include "ccusgr.mm"
include "wcel.mm"
include "cusgr.mm"
include "cv.mm"
include "cpr.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "iscusgredg.mm"
include "wss.mm"
include "cedg.mm"
include "cvtx.mm"
include "usgredgss.mm"
include "pweqi.mm"
include "rabeq.mm"
include "ax-mp.mm"
include "3sstr4g.mm"
include "adantr.mm"
include "wne.mm"
include "wrex.mm"
include "elss2prb.mm"
include "wi.mm"
include "weq.mm"
include "sneq.mm"
include "difeq2d.mm"
include "preq2.mm"
include "eleq1d.mm"
include "raleqbidv.mm"
include "rspcv.mm"
include "simpr.mm"
include "necom.mm"
include "biimpi.mm"
include "anim12i.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "preq1.mm"
include "syl.mm"
include "id.mm"
include "prcom.mm"
include "syl6req.mm"
include "biimpd.mm"
include "a1d.mm"
include "ad2antll.mm"
include "com23.mm"
include "3syld.mm"
include "ex.mm"
include "rexlimivv.mm"
include "com13.mm"
include "imp.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "sylbi.mm"

theorem cusgredg
  let vx: setvar x
  let cE: class E
  let cG: class G
  let cV: class V
  let vv: setvar v
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vy: setvar y
  let vz: setvar z
  assume iscusgrvtx.v: |- V = ( Vtx ` G )
  assume iscusgredg.v: |- E = ( Edg ` G )

  disjoint G x
  disjoint V x
  disjoint G v
  disjoint V v
  disjoint G k
  disjoint G n
  disjoint k n
  disjoint V k
  disjoint V n
  disjoint E n
  disjoint E p
  disjoint E v
  disjoint E y
  disjoint E z
  disjoint n p
  disjoint n v
  disjoint n y
  disjoint n z
  disjoint p v
  disjoint p y
  disjoint p z
  disjoint v y
  disjoint v z
  disjoint y z
  disjoint G p
  disjoint G y
  disjoint G z
  disjoint p x
  disjoint x y
  disjoint x z
  disjoint V p
  disjoint V y
  disjoint V z
  assert |- ( G e. ComplUSGraph -> E = { x e. ~P V | ( # ` x ) = 2 } )

  proof
    cG
    ccusgr
    wcel
    cG
    cusgr
    wcel
    #
    vn
    cv
    #
    vv
    cv
    #
    cpr
    #
    cE
    wcel
    #
    vn
    cV
    @2
    csn
    #
    cdif
    #
    wral
    #
    vv
    cV
    wral
    #
    wa
    #
    cE
    vx
    cv
    chash
    cfv
    c2
    wceq
    #
    vx
    cV
    cpw
    #
    crab
    #
    wceq
    vv
    vn
    cE
    cG
    cV
    iscusgrvtx.v
    iscusgredg.v
    iscusgredg
    @9
    cE
    @12
    @0
    cE
    @12
    wss
    @8
    @0
    cG
    cedg
    cfv
    @10
    vx
    cG
    cvtx
    cfv
    #
    cpw
    #
    crab
    #
    cE
    @12
    vx
    cG
    usgredgss
    iscusgredg.v
    @11
    @14
    wceq
    @12
    @15
    wceq
    cV
    @13
    iscusgrvtx.v
    pweqi
    @10
    vx
    @11
    @14
    rabeq
    ax-mp
    3sstr4g
    adantr
    @9
    vp
    @12
    cE
    vp
    cv
    #
    @12
    wcel
    vy
    cv
    #
    vz
    cv
    #
    wne
    #
    @16
    @17
    @18
    cpr
    #
    wceq
    #
    wa
    #
    vz
    cV
    wrex
    vy
    cV
    wrex
    #
    @9
    @16
    cE
    wcel
    #
    vy
    vz
    vx
    @16
    cV
    elss2prb
    @0
    @8
    @23
    @24
    wi
    @23
    @8
    @0
    @24
    @22
    @8
    @0
    @24
    wi
    #
    wi
    #
    vy
    vz
    cV
    cV
    @17
    cV
    wcel
    #
    @18
    cV
    wcel
    #
    wa
    #
    @22
    @26
    @29
    @22
    wa
    #
    @8
    @1
    @17
    cpr
    #
    cE
    wcel
    #
    vn
    cV
    @17
    csn
    #
    cdif
    #
    wral
    #
    @18
    @17
    cpr
    #
    cE
    wcel
    #
    @25
    @29
    @8
    @35
    wi
    #
    @22
    @27
    @38
    @28
    @7
    @35
    vv
    @17
    cV
    vv
    vy
    weq
    #
    @4
    @32
    vn
    @6
    @34
    @39
    @5
    @33
    cV
    @2
    @17
    sneq
    difeq2d
    @39
    @3
    @31
    cE
    @2
    @17
    @1
    preq2
    eleq1d
    raleqbidv
    rspcv
    adantr
    adantr
    @30
    @18
    @34
    wcel
    #
    @35
    @37
    wi
    @30
    @28
    @18
    @17
    wne
    #
    wa
    @40
    @29
    @28
    @22
    @41
    @27
    @28
    simpr
    @19
    @41
    @21
    @19
    @41
    @17
    @18
    necom
    biimpi
    adantr
    anim12i
    @18
    cV
    @17
    eldifsn
    sylibr
    @32
    @37
    vn
    @18
    @34
    vn
    vz
    weq
    @31
    @36
    cE
    @1
    @18
    @17
    preq1
    eleq1d
    rspcv
    syl
    @30
    @0
    @37
    @24
    @21
    @0
    @37
    @24
    wi
    #
    wi
    @29
    @19
    @21
    @42
    @0
    @21
    @37
    @24
    @21
    @36
    @16
    cE
    @21
    @16
    @20
    @36
    @21
    id
    @17
    @18
    prcom
    syl6req
    eleq1d
    biimpd
    a1d
    ad2antll
    com23
    3syld
    ex
    rexlimivv
    com13
    imp
    syl5bi
    ssrdv
    eqssd
    sylbi
end
