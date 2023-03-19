include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "simpll1.mm"
include "simpll3.mm"
include "simpr.mm"
include "simplr.mm"
include "lplni.mm"
include "syl31anc.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wrex.mm"
include "cp0.mm"
include "wne.mm"
include "catm.mm"
include "wn.mm"
include "simpll2.mm"
include "eqid.mm"
include "lplnneat.mm"
include "sylancom.mm"
include "wceq.mm"
include "breq1.mm"
include "syl5ibcom.mm"
include "wb.mm"
include "isat2.mm"
include "syl2anc.mm"
include "sylibrd.mm"
include "necon3bd.mm"
include "mpd.mm"
include "lplnnelln.mm"
include "atcvrlln.mm"
include "adantr.mm"
include "mtbird.mm"
include "llnle.mm"
include "syl22anc.mm"
include "wi.mm"
include "simpr3.mm"
include "cops.mm"
include "hlop.mm"
include "syl.mm"
include "simpr2.mm"
include "llnbase.mm"
include "simpr1.mm"
include "cvrle.mm"
include "cpo.mm"
include "hlpos.mm"
include "postr.mm"
include "syl13anc.mm"
include "mp2and.mm"
include "llncvrlpln2.mm"
include "cvrcmp2.mm"
include "syl132anc.mm"
include "mpbid.mm"
include "eqeltrrd.mm"
include "3exp2.mm"
include "imp.mm"
include "rexlimdv.mm"
include "impbida.mm"

theorem llncvrlpln
  let cB: class B
  let cC: class C
  let cP: class P
  let cK: class K
  let cN: class N
  let cX: class X
  let cY: class Y
  let vz: setvar z
  assume llncvrlpln.b: |- B = ( Base ` K )
  assume llncvrlpln.c: |- C = ( <o ` K )
  assume llncvrlpln.n: |- N = ( LLines ` K )
  assume llncvrlpln.p: |- P = ( LPlanes ` K )


  assert |- ( ( ( K e. HL /\ X e. B /\ Y e. B ) /\ X C Y ) -> ( X e. N <-> Y e. P ) )

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
    cN
    wcel
    #
    cY
    cP
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
    cN
    cX
    cY
    llncvrlpln.b
    llncvrlpln.c
    llncvrlpln.n
    llncvrlpln.p
    lplni
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
    cN
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
    #
    @14
    @5
    @7
    @0
    @19
    @17
    @15
    cP
    cK
    cY
    @15
    eqid
    #
    llncvrlpln.p
    lplnneat
    sylancom
    @8
    @18
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
    @18
    @8
    @4
    @21
    @22
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
    @18
    @22
    wb
    @17
    @0
    @1
    @2
    @4
    @7
    simpll3
    @15
    cB
    cC
    chlt
    cY
    cK
    @13
    llncvrlpln.b
    @13
    eqid
    #
    llncvrlpln.c
    @20
    isat2
    syl2anc
    sylibrd
    necon3bd
    mpd
    @8
    @16
    cY
    cN
    wcel
    #
    @5
    @7
    @0
    @24
    wn
    @17
    cP
    cK
    cN
    cY
    llncvrlpln.n
    llncvrlpln.p
    lplnnelln
    sylancom
    @5
    @16
    @24
    wb
    @7
    @15
    cB
    cC
    cK
    cN
    cX
    cY
    llncvrlpln.b
    llncvrlpln.c
    @20
    llncvrlpln.n
    atcvrlln
    adantr
    mtbird
    vz
    @15
    cB
    cK
    @10
    cN
    cX
    @13
    llncvrlpln.b
    @10
    eqid
    #
    @23
    @20
    llncvrlpln.n
    llnle
    syl22anc
    @8
    @11
    @6
    vz
    cN
    @5
    @7
    @9
    cN
    wcel
    #
    @11
    @6
    wi
    wi
    @5
    @7
    @26
    @11
    @6
    @5
    @7
    @26
    @11
    w3a
    #
    wa
    #
    @9
    cX
    cN
    @28
    @11
    @9
    cX
    wceq
    #
    @5
    @7
    @26
    @11
    simpr3
    #
    @28
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
    @29
    wb
    @28
    @0
    @31
    @0
    @1
    @2
    @4
    @27
    simpll1
    #
    cK
    hlop
    syl
    @28
    @26
    @32
    @5
    @7
    @26
    @11
    simpr2
    #
    cB
    cK
    cN
    @9
    llncvrlpln.b
    llncvrlpln.n
    llnbase
    syl
    #
    @0
    @1
    @2
    @4
    @27
    simpll2
    #
    @0
    @1
    @2
    @4
    @27
    simpll3
    #
    @28
    @0
    @26
    @7
    @9
    cY
    @10
    wbr
    #
    @33
    @34
    @35
    @5
    @7
    @26
    @11
    simpr1
    @28
    @11
    cX
    cY
    @10
    wbr
    #
    @39
    @30
    @5
    @40
    @27
    chlt
    cB
    cC
    cK
    @10
    cX
    cY
    llncvrlpln.b
    @25
    llncvrlpln.c
    cvrle
    adantr
    @28
    cK
    cpo
    wcel
    #
    @32
    @1
    @2
    @11
    @40
    wa
    @39
    wi
    @28
    @0
    @41
    @34
    cK
    hlpos
    syl
    @36
    @37
    @38
    cB
    cK
    @10
    @9
    cX
    cY
    llncvrlpln.b
    @25
    postr
    syl13anc
    mp2and
    cC
    cP
    cK
    @10
    cN
    @9
    cY
    @25
    llncvrlpln.c
    llncvrlpln.n
    llncvrlpln.p
    llncvrlpln2
    syl31anc
    @3
    @4
    @27
    simplr
    cB
    cC
    cK
    @10
    @9
    cX
    cY
    llncvrlpln.b
    @25
    llncvrlpln.c
    cvrcmp2
    syl132anc
    mpbid
    @35
    eqeltrrd
    3exp2
    imp
    rexlimdv
    mpd
    impbida
end
