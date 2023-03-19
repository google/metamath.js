include "cdr.mm"
include "wcel.mm"
include "csubrg.mm"
include "cfv.mm"
include "wa.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cinvr.mm"
include "cbs.mm"
include "crg.mm"
include "cui.mm"
include "simpllr.mm"
include "subrgring.mm"
include "syl.mm"
include "c0g.mm"
include "wne.mm"
include "simpr.mm"
include "eldifsn.mm"
include "sylib.mm"
include "simpld.mm"
include "wceq.mm"
include "subrgbas.mm"
include "eleqtrd.mm"
include "simprd.mm"
include "subrg0.mm"
include "neeqtrd.mm"
include "wb.mm"
include "eqid.mm"
include "drngunit.mm"
include "ad2antlr.mm"
include "mpbir2and.mm"
include "ringinvcl.mm"
include "syl2anc.mm"
include "subrginv.mm"
include "3eltr4d.mm"
include "ralrimiva.mm"
include "cin.mm"
include "wss.mm"
include "subrguss.mm"
include "isdrng.mm"
include "simprbi.mm"
include "ad2antrr.mm"
include "sseqtrd.mm"
include "unitss.mm"
include "syl5sseqr.mm"
include "ssind.mm"
include "subrgss.mm"
include "difin2.mm"
include "sseqtr4d.mm"
include "simprl.mm"
include "sseldd.mm"
include "simprr.mm"
include "w3a.mm"
include "subrgunit.mm"
include "mpbir3and.mm"
include "expr.mm"
include "ralimdva.mm"
include "imp.mm"
include "dfss3.mm"
include "sylibr.mm"
include "eqssd.mm"
include "sneqd.mm"
include "difeq12d.mm"
include "eqtrd.mm"
include "sylanbrc.mm"
include "impbida.mm"

theorem issubdrg
  let vx: setvar x
  let cA: class A
  let cR: class R
  let cS: class S
  let cI: class I
  let c.0: class .0.
  assume issubdrg.s: |- S = ( R |`s A )
  assume issubdrg.z: |- .0. = ( 0g ` R )
  assume issubdrg.i: |- I = ( invr ` R )

  disjoint A x
  disjoint R x
  disjoint S x
  disjoint .0. x
  assert |- ( ( R e. DivRing /\ A e. ( SubRing ` R ) ) -> ( S e. DivRing <-> A. x e. ( A \ { .0. } ) ( I ` x ) e. A ) )

  proof
    cR
    cdr
    wcel
    #
    cA
    cR
    csubrg
    cfv
    wcel
    #
    wa
    #
    cS
    cdr
    wcel
    #
    vx
    cv
    #
    cI
    cfv
    #
    cA
    wcel
    #
    vx
    cA
    c.0
    csn
    #
    cdif
    #
    wral
    #
    @2
    @3
    wa
    #
    @6
    vx
    @8
    @10
    @4
    @8
    wcel
    #
    wa
    #
    @4
    cS
    cinvr
    cfv
    #
    cfv
    #
    cS
    cbs
    cfv
    #
    @5
    cA
    @12
    cS
    crg
    wcel
    #
    @4
    cS
    cui
    cfv
    #
    wcel
    #
    @14
    @15
    wcel
    @12
    @1
    @16
    @0
    @1
    @3
    @11
    simpllr
    #
    cA
    cR
    cS
    issubdrg.s
    subrgring
    #
    syl
    @12
    @18
    @4
    @15
    wcel
    #
    @4
    cS
    c0g
    cfv
    #
    wne
    #
    @12
    @4
    cA
    @15
    @12
    @4
    cA
    wcel
    #
    @4
    c.0
    wne
    #
    @12
    @11
    @24
    @25
    wa
    #
    @10
    @11
    simpr
    @4
    cA
    c.0
    eldifsn
    #
    sylib
    #
    simpld
    @12
    @1
    cA
    @15
    wceq
    #
    @19
    cA
    cR
    cS
    issubdrg.s
    subrgbas
    #
    syl
    #
    eleqtrd
    @12
    @4
    c.0
    @22
    @12
    @24
    @25
    @28
    simprd
    @12
    @1
    c.0
    @22
    wceq
    #
    @19
    cA
    cR
    cS
    c.0
    issubdrg.s
    issubdrg.z
    subrg0
    #
    syl
    neeqtrd
    @3
    @18
    @21
    @23
    wa
    wb
    @2
    @11
    @15
    cS
    @17
    @4
    @22
    @15
    eqid
    #
    @17
    eqid
    #
    @22
    eqid
    #
    drngunit
    ad2antlr
    mpbir2and
    #
    @15
    cS
    @17
    @13
    @4
    @35
    @13
    eqid
    #
    @34
    ringinvcl
    syl2anc
    @12
    @1
    @18
    @5
    @14
    wceq
    @19
    @37
    cA
    cR
    cS
    @17
    cI
    @13
    @4
    issubdrg.s
    issubdrg.i
    @35
    @38
    subrginv
    syl2anc
    @31
    3eltr4d
    ralrimiva
    @2
    @9
    wa
    #
    @16
    @17
    @15
    @22
    csn
    #
    cdif
    #
    wceq
    @3
    @1
    @16
    @0
    @9
    @20
    ad2antlr
    @39
    @17
    @8
    @41
    @39
    @17
    @8
    @39
    @17
    cR
    cbs
    cfv
    #
    @7
    cdif
    #
    cA
    cin
    #
    @8
    @39
    @17
    @43
    cA
    @39
    @17
    cR
    cui
    cfv
    #
    @43
    @1
    @17
    @45
    wss
    @0
    @9
    cA
    cR
    cS
    @45
    @17
    issubdrg.s
    @45
    eqid
    #
    @35
    subrguss
    ad2antlr
    @0
    @45
    @43
    wceq
    #
    @1
    @9
    @0
    cR
    crg
    wcel
    @47
    @42
    cR
    @45
    c.0
    @42
    eqid
    #
    @46
    issubdrg.z
    isdrng
    simprbi
    ad2antrr
    sseqtrd
    @39
    @15
    @17
    cA
    @15
    cS
    @17
    @34
    @35
    unitss
    @1
    @29
    @0
    @9
    @30
    ad2antlr
    #
    syl5sseqr
    ssind
    @39
    cA
    @42
    wss
    #
    @8
    @44
    wceq
    @1
    @50
    @0
    @9
    cA
    @42
    cR
    @48
    subrgss
    #
    ad2antlr
    cA
    @7
    @42
    difin2
    syl
    sseqtr4d
    @39
    @18
    vx
    @8
    wral
    #
    @8
    @17
    wss
    @2
    @9
    @52
    @2
    @6
    @18
    vx
    @8
    @2
    @11
    @6
    @18
    @2
    @11
    @6
    wa
    #
    wa
    #
    @18
    @4
    @45
    wcel
    #
    @24
    @6
    @54
    @55
    @4
    @42
    wcel
    #
    @25
    @54
    cA
    @42
    @4
    @1
    @50
    @0
    @53
    @51
    ad2antlr
    @54
    @24
    @25
    @54
    @11
    @26
    @2
    @11
    @6
    simprl
    @27
    sylib
    #
    simpld
    #
    sseldd
    @54
    @24
    @25
    @57
    simprd
    @0
    @55
    @56
    @25
    wa
    wb
    @1
    @53
    @42
    cR
    @45
    @4
    c.0
    @48
    @46
    issubdrg.z
    drngunit
    ad2antrr
    mpbir2and
    @58
    @2
    @11
    @6
    simprr
    @1
    @18
    @55
    @24
    @6
    w3a
    wb
    @0
    @53
    cA
    cR
    cS
    @45
    cI
    @17
    @4
    issubdrg.s
    @46
    @35
    issubdrg.i
    subrgunit
    ad2antlr
    mpbir3and
    expr
    ralimdva
    imp
    vx
    @8
    @17
    dfss3
    sylibr
    eqssd
    @39
    cA
    @15
    @7
    @40
    @49
    @39
    c.0
    @22
    @1
    @32
    @0
    @9
    @33
    ad2antlr
    sneqd
    difeq12d
    eqtrd
    @15
    cS
    @17
    @22
    @34
    @35
    @36
    isdrng
    sylanbrc
    impbida
end
