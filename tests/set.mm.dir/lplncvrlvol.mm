include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "simpll1.mm"
include "simpll3.mm"
include "simpr.mm"
include "simplr.mm"
include "lvoli.mm"
include "syl31anc.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wrex.mm"
include "cp0.mm"
include "wne.mm"
include "catm.mm"
include "wn.mm"
include "clln.mm"
include "simpll2.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "latref.mm"
include "syl2anc.mm"
include "adantr.mm"
include "lvolnleat.mm"
include "syl3anc.mm"
include "ex.mm"
include "mt2d.mm"
include "wceq.mm"
include "breq1.mm"
include "syl5ibcom.mm"
include "wb.mm"
include "isat2.mm"
include "sylibrd.mm"
include "necon3bd.mm"
include "mpd.mm"
include "lvolnelln.mm"
include "sylancom.mm"
include "simpllr.mm"
include "llni.mm"
include "mtand.mm"
include "lvolnelpln.mm"
include "llncvrlpln.mm"
include "mtbird.mm"
include "lplnle.mm"
include "syl23anc.mm"
include "wi.mm"
include "simpr3.mm"
include "cops.mm"
include "hlop.mm"
include "simpr2.mm"
include "lplnbase.mm"
include "simpr1.mm"
include "cvrle.mm"
include "cpo.mm"
include "hlpos.mm"
include "postr.mm"
include "syl13anc.mm"
include "mp2and.mm"
include "lplncvrlvol2.mm"
include "cvrcmp2.mm"
include "syl132anc.mm"
include "mpbid.mm"
include "eqeltrrd.mm"
include "3exp2.mm"
include "imp.mm"
include "rexlimdv.mm"
include "impbida.mm"

theorem lplncvrlvol
  let cB: class B
  let cC: class C
  let cP: class P
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let vz: setvar z
  assume lplncvrlvol.b: |- B = ( Base ` K )
  assume lplncvrlvol.c: |- C = ( <o ` K )
  assume lplncvrlvol.p: |- P = ( LPlanes ` K )
  assume lplncvrlvol.v: |- V = ( LVols ` K )


  assert |- ( ( ( K e. HL /\ X e. B /\ Y e. B ) /\ X C Y ) -> ( X e. P <-> Y e. V ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    cC
    wbr
    #
    wa
    #
    cX
    cP
    wcel
    #
    cY
    cV
    wcel
    #
    @5
    @6
    wa
    @0
    @2
    @6
    @4
    @7
    @0
    @1
    @2
    @4
    @6
    simpll1
    @0
    @1
    @2
    @4
    @6
    simpll3
    @5
    @6
    simpr
    @3
    @4
    @6
    simplr
    cB
    cC
    chlt
    cP
    cK
    cV
    cX
    cY
    lplncvrlvol.b
    lplncvrlvol.c
    lplncvrlvol.p
    lplncvrlvol.v
    lvoli
    syl31anc
    @5
    @7
    wa
    #
    vz
    cv
    #
    cX
    cK
    cple
    cfv
    #
    wbr
    #
    vz
    cP
    wrex
    #
    @6
    @8
    @0
    @1
    cX
    cK
    cp0
    cfv
    #
    wne
    #
    cX
    cK
    catm
    cfv
    #
    wcel
    #
    wn
    cX
    cK
    clln
    cfv
    #
    wcel
    #
    wn
    @12
    @0
    @1
    @2
    @4
    @7
    simpll1
    #
    @0
    @1
    @2
    @4
    @7
    simpll2
    @8
    cY
    @15
    wcel
    #
    wn
    @14
    @8
    @20
    cY
    cY
    @10
    wbr
    #
    @8
    cK
    clat
    wcel
    #
    @2
    @21
    @8
    @0
    @22
    @19
    cK
    hllat
    syl
    @0
    @1
    @2
    @4
    @7
    simpll3
    #
    cB
    cK
    @10
    cY
    lplncvrlvol.b
    @10
    eqid
    #
    latref
    syl2anc
    @8
    @20
    @21
    wn
    #
    @8
    @20
    wa
    @0
    @7
    @20
    @25
    @8
    @0
    @20
    @19
    adantr
    @5
    @7
    @20
    simplr
    @8
    @20
    simpr
    @15
    cY
    cK
    @10
    cV
    cY
    @24
    @15
    eqid
    #
    lplncvrlvol.v
    lvolnleat
    syl3anc
    ex
    mt2d
    @8
    @20
    cX
    @13
    @8
    cX
    @13
    wceq
    #
    @13
    cY
    cC
    wbr
    #
    @20
    @8
    @4
    @27
    @28
    @3
    @4
    @7
    simplr
    cX
    @13
    cY
    cC
    breq1
    syl5ibcom
    @8
    @0
    @2
    @20
    @28
    wb
    @19
    @23
    @15
    cB
    cC
    chlt
    cY
    cK
    @13
    lplncvrlvol.b
    @13
    eqid
    #
    lplncvrlvol.c
    @26
    isat2
    syl2anc
    sylibrd
    necon3bd
    mpd
    @8
    @16
    cY
    @17
    wcel
    #
    @5
    @7
    @0
    @30
    wn
    @19
    cK
    @17
    cV
    cY
    @17
    eqid
    #
    lplncvrlvol.v
    lvolnelln
    sylancom
    @8
    @16
    wa
    @0
    @2
    @16
    @4
    @30
    @8
    @0
    @16
    @19
    adantr
    @8
    @2
    @16
    @23
    adantr
    @8
    @16
    simpr
    @3
    @4
    @7
    @16
    simpllr
    @15
    cB
    cC
    chlt
    cX
    cK
    @17
    cY
    lplncvrlvol.b
    lplncvrlvol.c
    @26
    @31
    llni
    syl31anc
    mtand
    @8
    @18
    cY
    cP
    wcel
    #
    @5
    @7
    @0
    @32
    wn
    @19
    cP
    cK
    cV
    cY
    lplncvrlvol.p
    lplncvrlvol.v
    lvolnelpln
    sylancom
    @5
    @18
    @32
    wb
    @7
    cB
    cC
    cP
    cK
    @17
    cX
    cY
    lplncvrlvol.b
    lplncvrlvol.c
    @31
    lplncvrlvol.p
    llncvrlpln
    adantr
    mtbird
    vz
    @15
    cB
    cP
    cK
    @10
    @17
    cX
    @13
    lplncvrlvol.b
    @24
    @29
    @26
    @31
    lplncvrlvol.p
    lplnle
    syl23anc
    @8
    @11
    @6
    vz
    cP
    @5
    @7
    @9
    cP
    wcel
    #
    @11
    @6
    wi
    wi
    @5
    @7
    @33
    @11
    @6
    @5
    @7
    @33
    @11
    w3a
    #
    wa
    #
    @9
    cX
    cP
    @35
    @11
    @9
    cX
    wceq
    #
    @5
    @7
    @33
    @11
    simpr3
    #
    @35
    cK
    cops
    wcel
    #
    @9
    cB
    wcel
    #
    @1
    @2
    @9
    cY
    cC
    wbr
    #
    @4
    @11
    @36
    wb
    @35
    @0
    @38
    @0
    @1
    @2
    @4
    @34
    simpll1
    #
    cK
    hlop
    syl
    @35
    @33
    @39
    @5
    @7
    @33
    @11
    simpr2
    #
    cB
    cP
    cK
    @9
    lplncvrlvol.b
    lplncvrlvol.p
    lplnbase
    syl
    #
    @0
    @1
    @2
    @4
    @34
    simpll2
    #
    @0
    @1
    @2
    @4
    @34
    simpll3
    #
    @35
    @0
    @33
    @7
    @9
    cY
    @10
    wbr
    #
    @40
    @41
    @42
    @5
    @7
    @33
    @11
    simpr1
    @35
    @11
    cX
    cY
    @10
    wbr
    #
    @46
    @37
    @5
    @47
    @34
    chlt
    cB
    cC
    cK
    @10
    cX
    cY
    lplncvrlvol.b
    @24
    lplncvrlvol.c
    cvrle
    adantr
    @35
    cK
    cpo
    wcel
    #
    @39
    @1
    @2
    @11
    @47
    wa
    @46
    wi
    @35
    @0
    @48
    @41
    cK
    hlpos
    syl
    @43
    @44
    @45
    cB
    cK
    @10
    @9
    cX
    cY
    lplncvrlvol.b
    @24
    postr
    syl13anc
    mp2and
    cC
    cP
    cK
    @10
    cV
    @9
    cY
    @24
    lplncvrlvol.c
    lplncvrlvol.p
    lplncvrlvol.v
    lplncvrlvol2
    syl31anc
    @3
    @4
    @34
    simplr
    cB
    cC
    cK
    @10
    @9
    cX
    cY
    lplncvrlvol.b
    @24
    lplncvrlvol.c
    cvrcmp2
    syl132anc
    mpbid
    @42
    eqeltrrd
    3exp2
    imp
    rexlimdv
    mpd
    impbida
end
