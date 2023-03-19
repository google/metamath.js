include "cmnd.mm"
include "wcel.mm"
include "c1.mm"
include "wceq.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "c0g.mm"
include "cfv.mm"
include "csn.mm"
include "cv.mm"
include "cmg.mm"
include "co.mm"
include "simplr.mm"
include "oveq1d.mm"
include "eqid.mm"
include "gexid.mm"
include "adantl.mm"
include "mulg1.mm"
include "3eqtr3rd.mm"
include "velsn.mm"
include "sylibr.mm"
include "ex.mm"
include "ssrdv.mm"
include "mndidcl.mm"
include "adantr.mm"
include "snssd.mm"
include "eqssd.mm"
include "fvex.mm"
include "ensn1.mm"
include "syl6eqbr.mm"
include "cfz.mm"
include "cn.mm"
include "wral.mm"
include "simpl.mm"
include "1nn.mm"
include "a1i.mm"
include "en1eqsn.mm"
include "sylan.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "sylib.mm"
include "eqtrd.mm"
include "ralrimiva.mm"
include "gexlem2.mm"
include "syl3anc.mm"
include "elfz1eq.mm"
include "syl.mm"
include "impbida.mm"

theorem gex1
  let cE: class E
  let cG: class G
  let cX: class X
  let vx: setvar x
  assume gexcl2.1: |- X = ( Base ` G )
  assume gexcl2.2: |- E = ( gEx ` G )


  assert |- ( G e. Mnd -> ( E = 1 <-> X ~~ 1o ) )

  proof
    cG
    cmnd
    wcel
    #
    cE
    c1
    wceq
    #
    cX
    c1o
    cen
    wbr
    #
    @0
    @1
    wa
    #
    cX
    cG
    c0g
    cfv
    #
    csn
    #
    c1o
    cen
    @3
    cX
    @5
    @3
    vx
    cX
    @5
    @3
    vx
    cv
    #
    cX
    wcel
    #
    @6
    @5
    wcel
    #
    @3
    @7
    wa
    #
    @6
    @4
    wceq
    #
    @8
    @9
    cE
    @6
    cG
    cmg
    cfv
    #
    co
    #
    c1
    @6
    @11
    co
    #
    @4
    @6
    @9
    cE
    c1
    @6
    @11
    @0
    @1
    @7
    simplr
    oveq1d
    @7
    @12
    @4
    wceq
    @3
    @6
    @11
    cE
    cG
    cX
    @4
    gexcl2.1
    gexcl2.2
    @11
    eqid
    #
    @4
    eqid
    #
    gexid
    adantl
    @7
    @13
    @6
    wceq
    #
    @3
    cX
    @11
    cG
    @6
    gexcl2.1
    @14
    mulg1
    #
    adantl
    3eqtr3rd
    vx
    @4
    velsn
    #
    sylibr
    ex
    ssrdv
    @3
    @4
    cX
    @0
    @4
    cX
    wcel
    #
    @1
    cX
    cG
    @4
    gexcl2.1
    @15
    mndidcl
    #
    adantr
    snssd
    eqssd
    @4
    cG
    c0g
    fvex
    ensn1
    syl6eqbr
    @0
    @2
    wa
    #
    cE
    c1
    c1
    cfz
    co
    wcel
    #
    @1
    @21
    @0
    c1
    cn
    wcel
    #
    @13
    @4
    wceq
    #
    vx
    cX
    wral
    @22
    @0
    @2
    simpl
    @23
    @21
    1nn
    a1i
    @21
    @24
    vx
    cX
    @21
    @7
    wa
    #
    @13
    @6
    @4
    @7
    @16
    @21
    @17
    adantl
    @25
    @8
    @10
    @21
    @7
    @8
    @21
    cX
    @5
    @6
    @0
    @19
    @2
    cX
    @5
    wceq
    @20
    @4
    cX
    en1eqsn
    sylan
    eleq2d
    biimpa
    @18
    sylib
    eqtrd
    ralrimiva
    vx
    @11
    cE
    cG
    c1
    cmnd
    cX
    @4
    gexcl2.1
    gexcl2.2
    @14
    @15
    gexlem2
    syl3anc
    cE
    c1
    elfz1eq
    syl
    impbida
end
