include "cfrgr.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cvtxdg.mm"
include "wne.mm"
include "cv.mm"
include "ciedg.mm"
include "cdm.mm"
include "crab.mm"
include "cusgr.mm"
include "wceq.mm"
include "frgrusgr.mm"
include "anim1i.mm"
include "adantr.mm"
include "eqid.mm"
include "vtxdusgrval.mm"
include "syl.mm"
include "wreu.mm"
include "wn.mm"
include "cpr.mm"
include "cedg.mm"
include "w3a.mm"
include "wrex.mm"
include "wral.mm"
include "3cyclfrgrrn2.mm"
include "adantlr.mm"
include "wi.mm"
include "preq1.mm"
include "eleq1d.mm"
include "preq2.mm"
include "3anbi13d.mm"
include "anbi2d.mm"
include "2rexbidv.mm"
include "rspcva.mm"
include "adantl.mm"
include "simplll.mm"
include "3simpb.mm"
include "ad3antlr.mm"
include "usgr2edg1.mm"
include "syl21anc.mm"
include "a1d.mm"
include "ex.mm"
include "a1i.mm"
include "rexlimivv.mm"
include "pm2.43a.mm"
include "com24.mm"
include "com3r.mm"
include "imp31.mm"
include "mpd.mm"
include "csn.mm"
include "wex.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "dmex.mm"
include "rabexg.mm"
include "hash1snb.mm"
include "3syl.mm"
include "reusn.mm"
include "syl6bbr.mm"
include "necon3abid.mm"
include "mpbird.mm"
include "eqnetrd.mm"

theorem vdgn1frgrv2
  let cG: class G
  let cN: class N
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vx: setvar x
  let vi: setvar i
  assume vdn1frgrv2.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. FriendGraph /\ N e. V ) -> ( 1 < ( # ` V ) -> ( ( VtxDeg ` G ) ` N ) =/= 1 ) )

  proof
    cG
    cfrgr
    wcel
    #
    cN
    cV
    wcel
    #
    wa
    #
    c1
    cV
    chash
    cfv
    clt
    wbr
    #
    cN
    cG
    cvtxdg
    cfv
    #
    cfv
    #
    c1
    wne
    @2
    @3
    wa
    #
    @5
    cN
    vx
    cv
    cG
    ciedg
    cfv
    #
    cfv
    wcel
    #
    vx
    @7
    cdm
    #
    crab
    #
    chash
    cfv
    #
    c1
    @6
    cG
    cusgr
    wcel
    #
    @1
    wa
    #
    @5
    @11
    wceq
    @2
    @13
    @3
    @0
    @12
    @1
    cG
    frgrusgr
    #
    anim1i
    adantr
    vx
    @9
    @4
    cN
    cG
    @7
    cV
    vdn1frgrv2.v
    @7
    eqid
    #
    @9
    eqid
    @4
    eqid
    vtxdusgrval
    syl
    @6
    @11
    c1
    wne
    @8
    vx
    @9
    wreu
    #
    wn
    #
    @6
    vb
    cv
    #
    vc
    cv
    #
    wne
    #
    va
    cv
    #
    @18
    cpr
    #
    cG
    cedg
    cfv
    #
    wcel
    #
    @18
    @19
    cpr
    @23
    wcel
    #
    @19
    @21
    cpr
    #
    @23
    wcel
    #
    w3a
    #
    wa
    #
    vc
    cV
    wrex
    vb
    cV
    wrex
    #
    va
    cV
    wral
    #
    @17
    @0
    @3
    @31
    @1
    @23
    cG
    cV
    va
    vb
    vc
    vdn1frgrv2.v
    @23
    eqid
    #
    3cyclfrgrrn2
    adantlr
    @0
    @1
    @3
    @31
    @17
    wi
    #
    @1
    @3
    @0
    @33
    @1
    @31
    @0
    @3
    @17
    @31
    @1
    @0
    @3
    @17
    wi
    #
    wi
    #
    @1
    @31
    @1
    @35
    wi
    #
    @1
    @31
    wa
    @20
    cN
    @18
    cpr
    #
    @23
    wcel
    #
    @25
    @19
    cN
    cpr
    #
    @23
    wcel
    #
    w3a
    #
    wa
    #
    vc
    cV
    wrex
    vb
    cV
    wrex
    #
    @36
    @30
    @43
    va
    cN
    cV
    @21
    cN
    wceq
    #
    @29
    @42
    vb
    vc
    cV
    cV
    @44
    @28
    @41
    @20
    @44
    @24
    @38
    @27
    @40
    @25
    @44
    @22
    @37
    @23
    @21
    cN
    @18
    preq1
    eleq1d
    @44
    @26
    @39
    @23
    @21
    cN
    @19
    preq2
    eleq1d
    3anbi13d
    anbi2d
    2rexbidv
    rspcva
    @42
    @36
    vb
    vc
    cV
    cV
    @42
    @36
    wi
    @18
    cV
    wcel
    @19
    cV
    wcel
    wa
    @42
    @1
    @35
    @42
    @1
    wa
    #
    @0
    @34
    @45
    @0
    wa
    #
    @17
    @3
    @46
    @12
    @20
    @38
    @40
    wa
    #
    @17
    @0
    @12
    @45
    @14
    adantl
    @20
    @41
    @1
    @0
    simplll
    @41
    @47
    @20
    @1
    @0
    @38
    @25
    @40
    3simpb
    ad3antlr
    vx
    @18
    @19
    @23
    cG
    @7
    cN
    @15
    @32
    usgr2edg1
    syl21anc
    a1d
    ex
    ex
    a1i
    rexlimivv
    syl
    ex
    pm2.43a
    com24
    com3r
    imp31
    mpd
    @6
    @16
    @11
    c1
    @6
    @11
    c1
    wceq
    #
    @10
    vi
    cv
    csn
    wceq
    vi
    wex
    #
    @16
    @6
    @9
    cvv
    wcel
    #
    @10
    cvv
    wcel
    @48
    @49
    wb
    @50
    @6
    @7
    cG
    ciedg
    fvex
    dmex
    a1i
    @8
    vx
    @9
    cvv
    rabexg
    @10
    cvv
    vi
    hash1snb
    3syl
    @8
    vx
    vi
    @9
    reusn
    syl6bbr
    necon3abid
    mpbird
    eqnetrd
    ex
end
