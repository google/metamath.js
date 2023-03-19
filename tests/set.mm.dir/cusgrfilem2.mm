include "wcel.mm"
include "cv.mm"
include "cpr.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wceq.mm"
include "wreu.mm"
include "wf1o.mm"
include "wa.mm"
include "cpw.mm"
include "wne.mm"
include "wrex.mm"
include "eldifi.mm"
include "id.mm"
include "prelpwi.mm"
include "syl2anr.mm"
include "adantl.mm"
include "eldifsni.mm"
include "eqidd.mm"
include "jca.mm"
include "wb.mm"
include "neeq1.mm"
include "preq1.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcedv.mm"
include "sylc.mm"
include "crab.mm"
include "eleq2i.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "cbvrabv.mm"
include "elrab2.mm"
include "bitri.mm"
include "sylanbrc.mm"
include "ralrimiva.mm"
include "simpl.mm"
include "anim2i.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "wi.mm"
include "ad2antlr.mm"
include "vex.mm"
include "preqr1.mm"
include "equcomd.mm"
include "syl6bi.mm"
include "adantll.mm"
include "equcoms.mm"
include "biimpcd.mm"
include "impbid.mm"
include "ex.mm"
include "reximdv2.mm"
include "expimpd.mm"
include "reu6.mm"
include "3imtr4g.mm"
include "ralrimiv.mm"
include "f1ompt.mm"

theorem cusgrfilem2
  let vx: setvar x
  let cP: class P
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let va: setvar a
  let ve: setvar e
  let vv: setvar v
  assume cusgrfi.v: |- V = ( Vtx ` G )
  assume cusgrfi.p: |- P = { x e. ~P V | E. a e. V ( a =/= N /\ x = { a , N } ) }
  assume cusgrfi.f: |- F = ( x e. ( V \ { N } ) |-> { x , N } )

  disjoint G x
  disjoint N a
  disjoint N x
  disjoint a x
  disjoint V a
  disjoint V x
  disjoint P x
  disjoint F e
  disjoint N e
  disjoint a e
  disjoint e x
  disjoint N v
  disjoint a v
  disjoint v x
  disjoint P e
  disjoint V e
  disjoint V v
  assert |- ( N e. V -> F : ( V \ { N } ) -1-1-onto-> P )

  proof
    cN
    cV
    wcel
    #
    vx
    cv
    #
    cN
    cpr
    #
    cP
    wcel
    #
    vx
    cV
    cN
    csn
    #
    cdif
    #
    wral
    ve
    cv
    #
    @2
    wceq
    #
    vx
    @5
    wreu
    #
    ve
    cP
    wral
    @5
    cP
    cF
    wf1o
    @0
    @3
    vx
    @5
    @0
    @1
    @5
    wcel
    #
    wa
    #
    @2
    cV
    cpw
    #
    wcel
    #
    va
    cv
    #
    cN
    wne
    #
    @2
    @13
    cN
    cpr
    #
    wceq
    #
    wa
    #
    va
    cV
    wrex
    #
    @3
    @9
    @1
    cV
    wcel
    #
    @0
    @12
    @0
    @1
    cV
    @4
    eldifi
    #
    @0
    id
    @1
    cN
    cV
    prelpwi
    syl2anr
    @10
    @19
    @1
    cN
    wne
    #
    @2
    @2
    wceq
    #
    wa
    #
    @18
    @9
    @19
    @0
    @20
    adantl
    @10
    @21
    @22
    @9
    @21
    @0
    @1
    cV
    cN
    eldifsni
    adantl
    @10
    @2
    eqidd
    jca
    @19
    @17
    @23
    va
    @1
    cV
    @19
    id
    @13
    @1
    wceq
    #
    @17
    @23
    wb
    @19
    @24
    @14
    @21
    @16
    @22
    @13
    @1
    cN
    neeq1
    @24
    @15
    @2
    @2
    @13
    @1
    cN
    preq1
    #
    eqeq2d
    anbi12d
    adantl
    rspcedv
    sylc
    @3
    @2
    @14
    @1
    @15
    wceq
    #
    wa
    #
    va
    cV
    wrex
    #
    vx
    @11
    crab
    #
    wcel
    @12
    @18
    wa
    cP
    @29
    @2
    cusgrfi.p
    eleq2i
    @14
    vv
    cv
    #
    @15
    wceq
    #
    wa
    #
    va
    cV
    wrex
    #
    @18
    vv
    @2
    @11
    @29
    @30
    @2
    wceq
    #
    @32
    @17
    va
    cV
    @34
    @31
    @16
    @14
    @30
    @2
    @15
    eqeq1
    anbi2d
    rexbidv
    @28
    @33
    vx
    vv
    @11
    @1
    @30
    wceq
    #
    @27
    @32
    va
    cV
    @35
    @26
    @31
    @14
    @1
    @30
    @15
    eqeq1
    anbi2d
    rexbidv
    cbvrabv
    elrab2
    bitri
    sylanbrc
    ralrimiva
    @0
    @8
    ve
    cP
    @0
    @6
    @11
    wcel
    #
    @14
    @6
    @15
    wceq
    #
    wa
    #
    va
    cV
    wrex
    #
    wa
    @7
    @1
    @13
    wceq
    #
    wb
    #
    vx
    @5
    wral
    #
    va
    @5
    wrex
    #
    @6
    cP
    wcel
    @8
    @0
    @36
    @39
    @43
    @0
    @36
    wa
    #
    @38
    @42
    va
    cV
    @5
    @44
    @13
    cV
    wcel
    #
    @38
    wa
    #
    @13
    @5
    wcel
    #
    @42
    wa
    @44
    @46
    wa
    #
    @47
    @42
    @48
    @45
    @14
    wa
    #
    @47
    @46
    @49
    @44
    @38
    @14
    @45
    @14
    @37
    simpl
    anim2i
    adantl
    @13
    cV
    cN
    eldifsn
    sylibr
    @48
    @41
    vx
    @5
    @48
    @9
    wa
    @7
    @40
    @46
    @9
    @7
    @40
    wi
    @44
    @46
    @9
    wa
    @7
    @15
    @2
    wceq
    #
    @40
    @38
    @7
    @50
    wb
    #
    @45
    @9
    @37
    @51
    @14
    @6
    @15
    @2
    eqeq1
    adantl
    ad2antlr
    @50
    va
    vx
    @13
    @1
    cN
    va
    vex
    vx
    vex
    preqr1
    equcomd
    syl6bi
    adantll
    @46
    @40
    @7
    wi
    #
    @44
    @9
    @38
    @52
    @45
    @37
    @52
    @14
    @40
    @37
    @7
    @40
    @15
    @2
    @6
    @50
    va
    vx
    @25
    equcoms
    eqeq2d
    biimpcd
    adantl
    adantl
    ad2antlr
    impbid
    ralrimiva
    jca
    ex
    reximdv2
    expimpd
    @28
    @39
    vx
    @6
    @11
    cP
    @1
    @6
    wceq
    #
    @27
    @38
    va
    cV
    @53
    @26
    @37
    @14
    @1
    @6
    @15
    eqeq1
    anbi2d
    rexbidv
    cusgrfi.p
    elrab2
    @7
    vx
    va
    @5
    reu6
    3imtr4g
    ralrimiv
    vx
    ve
    @5
    cP
    @2
    cF
    cusgrfi.f
    f1ompt
    sylanbrc
end
