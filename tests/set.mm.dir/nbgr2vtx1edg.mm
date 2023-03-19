include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "wcel.mm"
include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wne.mm"
include "cpr.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "cvv.mm"
include "wb.mm"
include "cvtx.mm"
include "fvexi.mm"
include "hash2prb.mm"
include "ax-mp.mm"
include "wss.mm"
include "simpll.mm"
include "ancomd.mm"
include "simpl.mm"
include "necomd.mm"
include "ad2antlr.mm"
include "id.mm"
include "sseq2.mm"
include "adantl.mm"
include "ssid.mm"
include "a1i.mm"
include "rspcedvd.mm"
include "nbgrel.mm"
include "syl3anbrc.mm"
include "prcom.mm"
include "eqimssi.mm"
include "difprsn1.mm"
include "raleqdv.mm"
include "vex.mm"
include "eleq1.mm"
include "ralsn.mm"
include "syl6bb.mm"
include "difprsn2.mm"
include "anbi12d.mm"
include "adantr.mm"
include "mpbir2and.mm"
include "ex.mm"
include "difeq1.mm"
include "raleqbidv.mm"
include "sneq.mm"
include "difeq2d.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "ralpr.mm"
include "imbi12d.mm"
include "mpbird.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "imp.mm"

theorem nbgr2vtx1edg
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
  assert |- ( ( ( # ` V ) = 2 /\ V e. E ) -> A. v e. V A. n e. ( V \ { v } ) n e. ( G NeighbVtx v ) )

  proof
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
    @3
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
    @0
    va
    cv
    #
    vb
    cv
    #
    wne
    #
    cV
    @10
    @11
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
    @1
    @9
    wi
    #
    cV
    cvv
    wcel
    @0
    @16
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
    @15
    @17
    va
    vb
    cV
    cV
    @10
    cV
    wcel
    #
    @11
    cV
    wcel
    #
    wa
    #
    @15
    @17
    @20
    @15
    wa
    #
    @17
    @13
    cE
    wcel
    #
    @2
    cG
    @10
    cnbgr
    co
    #
    wcel
    #
    vn
    @13
    @10
    csn
    #
    cdif
    #
    wral
    #
    @2
    cG
    @11
    cnbgr
    co
    #
    wcel
    #
    vn
    @13
    @11
    csn
    #
    cdif
    #
    wral
    #
    wa
    #
    wi
    #
    @21
    @22
    @33
    @21
    @22
    wa
    #
    @33
    @11
    @23
    wcel
    #
    @10
    @28
    wcel
    #
    @35
    @19
    @18
    wa
    @11
    @10
    wne
    #
    @13
    ve
    cv
    #
    wss
    #
    ve
    cE
    wrex
    #
    @36
    @35
    @18
    @19
    @20
    @15
    @22
    simpll
    #
    ancomd
    @15
    @38
    @20
    @22
    @15
    @10
    @11
    @12
    @14
    simpl
    #
    necomd
    ad2antlr
    @22
    @41
    @21
    @22
    @40
    @13
    @13
    wss
    #
    ve
    @13
    cE
    @22
    id
    #
    @39
    @13
    wceq
    #
    @40
    @44
    wb
    @22
    @39
    @13
    @13
    sseq2
    adantl
    @44
    @22
    @13
    ssid
    a1i
    rspcedvd
    adantl
    ve
    cE
    cG
    @11
    cV
    @10
    nbgr2vtx1edg.v
    nbgr2vtx1edg.e
    nbgrel
    syl3anbrc
    @35
    @20
    @12
    @11
    @10
    cpr
    #
    @39
    wss
    #
    ve
    cE
    wrex
    #
    @37
    @42
    @15
    @12
    @20
    @22
    @43
    ad2antlr
    @22
    @49
    @21
    @22
    @48
    @47
    @13
    wss
    #
    ve
    @13
    cE
    @45
    @46
    @48
    @50
    wb
    @22
    @39
    @13
    @47
    sseq2
    adantl
    @50
    @22
    @47
    @13
    @11
    @10
    prcom
    eqimssi
    a1i
    rspcedvd
    adantl
    ve
    cE
    cG
    @10
    cV
    @11
    nbgr2vtx1edg.v
    nbgr2vtx1edg.e
    nbgrel
    syl3anbrc
    @15
    @33
    @36
    @37
    wa
    wb
    #
    @20
    @22
    @12
    @51
    @14
    @12
    @27
    @36
    @32
    @37
    @12
    @27
    @24
    vn
    @30
    wral
    @36
    @12
    @24
    vn
    @26
    @30
    @10
    @11
    difprsn1
    raleqdv
    @24
    @36
    vn
    @11
    vb
    vex
    #
    @2
    @11
    @23
    eleq1
    ralsn
    syl6bb
    @12
    @32
    @29
    vn
    @25
    wral
    @37
    @12
    @29
    vn
    @31
    @25
    @10
    @11
    difprsn2
    raleqdv
    @29
    @37
    vn
    @10
    va
    vex
    #
    @2
    @10
    @28
    eleq1
    ralsn
    syl6bb
    anbi12d
    adantr
    ad2antlr
    mpbir2and
    ex
    @15
    @17
    @34
    wb
    #
    @20
    @14
    @54
    @12
    @14
    @1
    @22
    @9
    @33
    cV
    @13
    cE
    eleq1
    @14
    @9
    @5
    vn
    @13
    @6
    cdif
    #
    wral
    #
    vv
    @13
    wral
    @33
    @14
    @8
    @56
    vv
    cV
    @13
    @14
    id
    @14
    @5
    vn
    @7
    @55
    cV
    @13
    @6
    difeq1
    raleqdv
    raleqbidv
    @56
    @27
    @32
    vv
    @10
    @11
    @53
    @52
    @3
    @10
    wceq
    #
    @5
    @24
    vn
    @55
    @26
    @57
    @6
    @25
    @13
    @3
    @10
    sneq
    difeq2d
    @57
    @4
    @23
    @2
    @3
    @10
    cG
    cnbgr
    oveq2
    eleq2d
    raleqbidv
    @3
    @11
    wceq
    #
    @5
    @29
    vn
    @55
    @31
    @58
    @6
    @30
    @13
    @3
    @11
    sneq
    difeq2d
    @58
    @4
    @28
    @2
    @3
    @11
    cG
    cnbgr
    oveq2
    eleq2d
    raleqbidv
    ralpr
    syl6bb
    imbi12d
    adantl
    adantl
    mpbird
    ex
    rexlimivv
    sylbi
    imp
end
