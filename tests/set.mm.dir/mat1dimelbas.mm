include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wrex.mm"
include "cmap.mm"
include "co.mm"
include "cfn.mm"
include "wb.mm"
include "snfi.mm"
include "simpl.mm"
include "matbas2.mm"
include "eqcomd.mm"
include "eleq2d.mm"
include "sylancr.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "snex.mm"
include "pm3.2i.mm"
include "xpexg.mm"
include "mp1i.mm"
include "elmapg.mm"
include "bitrd.mm"
include "xpsng.mm"
include "anidms.mm"
include "adantl.mm"
include "feq2d.mm"
include "opex.mm"
include "fsn2.mm"
include "risset.mm"
include "eqcom.mm"
include "rexbii.mm"
include "sylbb.mm"
include "ad2antrl.mm"
include "eqeq1.mm"
include "sneqbg.mm"
include "ax-mp.mm"
include "eqid.mm"
include "vex.mm"
include "opth2.mm"
include "mpbiran.mm"
include "bitri.mm"
include "a1i.mm"
include "rexbidv.mm"
include "mpbird.mm"
include "ex.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "wf1o.mm"
include "f1o2sn.mm"
include "f1of.mm"
include "syl.mm"
include "adantll.mm"
include "wss.mm"
include "snssi.mm"
include "fssd.mm"
include "feq1.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "impbid.mm"
include "eqcomi.mm"
include "opeq1i.mm"
include "sneqi.mm"
include "eqeq2i.mm"

theorem mat1dimelbas
  let cA: class A
  let cB: class B
  let cR: class R
  let cE: class E
  let cM: class M
  let cO: class O
  let cV: class V
  let vr: setvar r
  assume mat1dim.a: |- A = ( { E } Mat R )
  assume mat1dim.b: |- B = ( Base ` R )
  assume mat1dim.o: |- O = <. E , E >.

  disjoint B r
  disjoint E r
  disjoint M r
  disjoint R r
  disjoint V r
  assert |- ( ( R e. Ring /\ E e. V ) -> ( M e. ( Base ` A ) <-> E. r e. B M = { <. O , r >. } ) )

  proof
    cR
    crg
    wcel
    #
    cE
    cV
    wcel
    #
    wa
    #
    cM
    cA
    cbs
    cfv
    #
    wcel
    #
    cE
    csn
    #
    @5
    cxp
    #
    cB
    cM
    wf
    #
    cM
    cO
    vr
    cv
    #
    cop
    #
    csn
    #
    wceq
    #
    vr
    cB
    wrex
    #
    @2
    @4
    cM
    cB
    @6
    cmap
    co
    #
    wcel
    #
    @7
    @2
    @5
    cfn
    wcel
    #
    @0
    @4
    @14
    wb
    cE
    snfi
    @0
    @1
    simpl
    @15
    @0
    wa
    #
    @3
    @13
    cM
    @16
    @13
    @3
    cA
    cR
    cB
    @5
    crg
    mat1dim.a
    mat1dim.b
    matbas2
    eqcomd
    eleq2d
    sylancr
    @2
    cB
    cvv
    wcel
    @6
    cvv
    wcel
    #
    @14
    @7
    wb
    cB
    cR
    cbs
    cfv
    cvv
    mat1dim.b
    cR
    cbs
    fvex
    eqeltri
    @5
    cvv
    wcel
    #
    @18
    wa
    @17
    @2
    @18
    @18
    cE
    snex
    #
    @19
    pm3.2i
    @5
    @5
    cvv
    cvv
    xpexg
    mp1i
    cB
    @6
    cM
    cvv
    cvv
    elmapg
    sylancr
    bitrd
    @2
    @7
    cM
    cE
    cE
    cop
    #
    @8
    cop
    #
    csn
    #
    wceq
    #
    vr
    cB
    wrex
    #
    @12
    @2
    @7
    @24
    @2
    @7
    @20
    csn
    #
    cB
    cM
    wf
    #
    @24
    @2
    @6
    @25
    cB
    cM
    @1
    @6
    @25
    wceq
    #
    @0
    @1
    @27
    cE
    cE
    cV
    cV
    xpsng
    anidms
    adantl
    feq2d
    @26
    @20
    cM
    cfv
    #
    cB
    wcel
    #
    cM
    @20
    @28
    cop
    #
    csn
    #
    wceq
    #
    wa
    #
    @2
    @24
    @20
    cB
    cM
    cE
    cE
    opex
    #
    fsn2
    @2
    @33
    @24
    @2
    @33
    wa
    #
    @24
    @28
    @8
    wceq
    #
    vr
    cB
    wrex
    #
    @29
    @37
    @2
    @32
    @29
    @8
    @28
    wceq
    #
    vr
    cB
    wrex
    @37
    vr
    @28
    cB
    risset
    @38
    @36
    vr
    cB
    @8
    @28
    eqcom
    rexbii
    sylbb
    ad2antrl
    @35
    @23
    @36
    vr
    cB
    @33
    @23
    @36
    wb
    #
    @2
    @32
    @39
    @29
    @32
    @23
    @31
    @22
    wceq
    #
    @36
    cM
    @31
    @22
    eqeq1
    @40
    @36
    wb
    @32
    @40
    @30
    @21
    wceq
    #
    @36
    @30
    cvv
    wcel
    @40
    @41
    wb
    @20
    @28
    opex
    @30
    @21
    cvv
    sneqbg
    ax-mp
    @41
    @20
    @20
    wceq
    @36
    @20
    eqid
    @20
    @28
    @20
    @8
    @34
    vr
    vex
    opth2
    mpbiran
    bitri
    a1i
    bitrd
    adantl
    adantl
    rexbidv
    mpbird
    ex
    syl5bi
    sylbid
    @2
    @23
    @7
    vr
    cB
    @2
    @8
    cB
    wcel
    #
    wa
    #
    @7
    @23
    @6
    cB
    @22
    wf
    @43
    @6
    @8
    csn
    #
    cB
    @22
    @1
    @42
    @6
    @44
    @22
    wf
    #
    @0
    @1
    @42
    wa
    @6
    @44
    @22
    wf1o
    @45
    cE
    cV
    cB
    @8
    f1o2sn
    @6
    @44
    @22
    f1of
    syl
    adantll
    @42
    @44
    cB
    wss
    @2
    @8
    cB
    snssi
    adantl
    fssd
    @6
    cB
    cM
    @22
    feq1
    syl5ibrcom
    rexlimdva
    impbid
    @2
    @23
    @11
    vr
    cB
    @23
    @11
    wb
    @2
    @22
    @10
    cM
    @21
    @9
    @20
    cO
    @8
    cO
    @20
    mat1dim.o
    eqcomi
    opeq1i
    sneqi
    eqeq2i
    a1i
    rexbidv
    bitrd
    bitrd
end
