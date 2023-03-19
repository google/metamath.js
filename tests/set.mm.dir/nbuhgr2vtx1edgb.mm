include "cuhgr.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wb.mm"
include "wne.mm"
include "cpr.mm"
include "wa.mm"
include "wrex.mm"
include "cvv.mm"
include "cvtx.mm"
include "fvexi.mm"
include "hash2prb.mm"
include "ax-mp.mm"
include "wss.mm"
include "simpr.mm"
include "ancomd.mm"
include "ad2antrr.mm"
include "id.mm"
include "necomd.mm"
include "adantr.mm"
include "ad2antlr.mm"
include "prcom.mm"
include "eleq1i.mm"
include "biimpi.mm"
include "sseq2.mm"
include "adantl.mm"
include "eqimssi.mm"
include "a1i.mm"
include "rspcedvd.mm"
include "nbgrel.mm"
include "syl3anbrc.mm"
include "simplrl.mm"
include "jca.mm"
include "ex.mm"
include "wi.mm"
include "nbuhgr2vtx1edgblem.mm"
include "3exp.mm"
include "adantld.mm"
include "imp.mm"
include "impbid.mm"
include "eleq1.mm"
include "difeq1.mm"
include "raleqdv.mm"
include "raleqbidv.mm"
include "vex.mm"
include "sneq.mm"
include "difeq2d.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "ralpr.mm"
include "difprsn1.mm"
include "ralsn.mm"
include "syl6bb.mm"
include "difprsn2.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "sylan9bbr.mm"
include "bibi12d.mm"
include "mpbird.mm"
include "rexlimdvva.mm"
include "syl5bi.mm"

theorem nbuhgr2vtx1edgb
  let vv: setvar v
  let vn: setvar n
  let cE: class E
  let cG: class G
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let ve: setvar e
  assume nbgr2vtx1edg.v: |- V = ( Vtx ` G )
  assume nbgr2vtx1edg.e: |- E = ( Edg ` G )

  disjoint E n
  disjoint G n
  disjoint G v
  disjoint n v
  disjoint V n
  disjoint V v
  disjoint E a
  disjoint E b
  disjoint E e
  disjoint a b
  disjoint a e
  disjoint a n
  disjoint b e
  disjoint b n
  disjoint e n
  disjoint G a
  disjoint G b
  disjoint G e
  disjoint a v
  disjoint b v
  disjoint e v
  disjoint V a
  disjoint V b
  disjoint V e
  assert |- ( ( G e. UHGraph /\ ( # ` V ) = 2 ) -> ( V e. E <-> A. v e. V A. n e. ( V \ { v } ) n e. ( G NeighbVtx v ) ) )

  proof
    cG
    cuhgr
    wcel
    #
    cV
    chash
    cfv
    c2
    wceq
    #
    cV
    cE
    wcel
    #
    vn
    cv
    #
    cG
    vv
    cv
    #
    cnbgr
    co
    #
    wcel
    #
    vn
    cV
    @4
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
    wb
    #
    @1
    va
    cv
    #
    vb
    cv
    #
    wne
    #
    cV
    @12
    @13
    cpr
    #
    wceq
    #
    wa
    #
    vb
    cV
    wrex
    va
    cV
    wrex
    #
    @0
    @11
    cV
    cvv
    wcel
    @1
    @18
    wb
    cV
    cG
    cvtx
    nbgr2vtx1edg.v
    fvexi
    cV
    cvv
    va
    vb
    hash2prb
    ax-mp
    @0
    @17
    @11
    va
    vb
    cV
    cV
    @0
    @12
    cV
    wcel
    #
    @13
    cV
    wcel
    #
    wa
    #
    wa
    #
    @17
    @11
    @22
    @17
    wa
    #
    @11
    @15
    cE
    wcel
    #
    @13
    cG
    @12
    cnbgr
    co
    #
    wcel
    #
    @12
    cG
    @13
    cnbgr
    co
    #
    wcel
    #
    wa
    #
    wb
    #
    @23
    @24
    @29
    @23
    @24
    @29
    @23
    @24
    wa
    #
    @26
    @28
    @31
    @20
    @19
    wa
    #
    @13
    @12
    wne
    #
    @15
    ve
    cv
    #
    wss
    #
    ve
    cE
    wrex
    #
    @26
    @22
    @32
    @17
    @24
    @22
    @19
    @20
    @0
    @21
    simpr
    #
    ancomd
    ad2antrr
    @17
    @33
    @22
    @24
    @14
    @33
    @16
    @14
    @12
    @13
    @14
    id
    necomd
    adantr
    ad2antlr
    @24
    @36
    @23
    @24
    @35
    @15
    @13
    @12
    cpr
    #
    wss
    #
    ve
    @38
    cE
    @24
    @38
    cE
    wcel
    @15
    @38
    cE
    @12
    @13
    prcom
    #
    eleq1i
    biimpi
    @34
    @38
    wceq
    @35
    @39
    wb
    @24
    @34
    @38
    @15
    sseq2
    adantl
    @39
    @24
    @15
    @38
    @40
    eqimssi
    a1i
    rspcedvd
    adantl
    ve
    cE
    cG
    @13
    cV
    @12
    nbgr2vtx1edg.v
    nbgr2vtx1edg.e
    nbgrel
    syl3anbrc
    @31
    @21
    @14
    @38
    @34
    wss
    #
    ve
    cE
    wrex
    #
    @28
    @22
    @21
    @17
    @24
    @37
    ad2antrr
    @22
    @14
    @16
    @24
    simplrl
    @24
    @42
    @23
    @24
    @41
    @38
    @15
    wss
    #
    ve
    @15
    cE
    @24
    id
    @34
    @15
    wceq
    @41
    @43
    wb
    @24
    @34
    @15
    @38
    sseq2
    adantl
    @43
    @24
    @38
    @15
    @13
    @12
    prcom
    eqimssi
    a1i
    rspcedvd
    adantl
    ve
    cE
    cG
    @12
    cV
    @13
    nbgr2vtx1edg.v
    nbgr2vtx1edg.e
    nbgrel
    syl3anbrc
    jca
    ex
    @23
    @28
    @24
    @26
    @22
    @17
    @28
    @24
    wi
    #
    @22
    @16
    @44
    @14
    @0
    @16
    @44
    wi
    @21
    @0
    @16
    @28
    @24
    cE
    cG
    cV
    va
    vb
    nbgr2vtx1edg.v
    nbgr2vtx1edg.e
    nbuhgr2vtx1edgblem
    3exp
    adantr
    adantld
    imp
    adantld
    impbid
    @17
    @11
    @30
    wb
    @22
    @17
    @2
    @24
    @10
    @29
    @16
    @2
    @24
    wb
    @14
    cV
    @15
    cE
    eleq1
    adantl
    @16
    @10
    @6
    vn
    @15
    @7
    cdif
    #
    wral
    #
    vv
    @15
    wral
    #
    @14
    @29
    @16
    @9
    @46
    vv
    cV
    @15
    @16
    id
    @16
    @6
    vn
    @8
    @45
    cV
    @15
    @7
    difeq1
    raleqdv
    raleqbidv
    @47
    @3
    @25
    wcel
    #
    vn
    @15
    @12
    csn
    #
    cdif
    #
    wral
    #
    @3
    @27
    wcel
    #
    vn
    @15
    @13
    csn
    #
    cdif
    #
    wral
    #
    wa
    @14
    @29
    @46
    @51
    @55
    vv
    @12
    @13
    va
    vex
    #
    vb
    vex
    #
    @4
    @12
    wceq
    #
    @6
    @48
    vn
    @45
    @50
    @58
    @7
    @49
    @15
    @4
    @12
    sneq
    difeq2d
    @58
    @5
    @25
    @3
    @4
    @12
    cG
    cnbgr
    oveq2
    eleq2d
    raleqbidv
    @4
    @13
    wceq
    #
    @6
    @52
    vn
    @45
    @54
    @59
    @7
    @53
    @15
    @4
    @13
    sneq
    difeq2d
    @59
    @5
    @27
    @3
    @4
    @13
    cG
    cnbgr
    oveq2
    eleq2d
    raleqbidv
    ralpr
    @14
    @51
    @26
    @55
    @28
    @14
    @51
    @48
    vn
    @53
    wral
    @26
    @14
    @48
    vn
    @50
    @53
    @12
    @13
    difprsn1
    raleqdv
    @48
    @26
    vn
    @13
    @57
    @3
    @13
    @25
    eleq1
    ralsn
    syl6bb
    @14
    @55
    @52
    vn
    @49
    wral
    @28
    @14
    @52
    vn
    @54
    @49
    @12
    @13
    difprsn2
    raleqdv
    @52
    @28
    vn
    @12
    @56
    @3
    @12
    @27
    eleq1
    ralsn
    syl6bb
    anbi12d
    syl5bb
    sylan9bbr
    bibi12d
    adantl
    mpbird
    ex
    rexlimdvva
    syl5bi
    imp
end
