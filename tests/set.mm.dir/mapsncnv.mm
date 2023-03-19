include "cv.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "csn.mm"
include "cxp.mm"
include "ccnv.mm"
include "cmpt.mm"
include "wf.mm"
include "elmapi.mm"
include "snid.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "eqid.mm"
include "mapsnconst.mm"
include "jca.mm"
include "eleq1.mm"
include "sneq.mm"
include "xpeq2d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "fconst6g.mm"
include "snex.mm"
include "elmap.mm"
include "sylibr.mm"
include "vex.mm"
include "fvconst2.mm"
include "mp1i.mm"
include "eqcomd.mm"
include "fveq1.mm"
include "impbii.mm"
include "oveq2i.mm"
include "eleq2i.mm"
include "anbi1i.mm"
include "xpeq1i.mm"
include "eqeq2i.mm"
include "anbi2i.mm"
include "3bitr4i.mm"
include "opabbii.mm"
include "df-mpt.mm"
include "eqtri.mm"
include "cnveqi.mm"
include "cnvopab.mm"
include "3eqtr4i.mm"

theorem mapsncnv
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cS: class S
  let cF: class F
  let cX: class X
  assume mapsncnv.s: |- S = { X }
  assume mapsncnv.b: |- B e. _V
  assume mapsncnv.x: |- X e. _V
  assume mapsncnv.f: |- F = ( x e. ( B ^m S ) |-> ( x ` X ) )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint S x
  disjoint S y
  disjoint X y
  assert |- `' F = ( y e. B |-> ( S X. { y } ) )

  proof
    vx
    cv
    #
    cB
    cS
    cmap
    co
    #
    wcel
    #
    vy
    cv
    #
    cX
    @0
    cfv
    #
    wceq
    #
    wa
    #
    vy
    vx
    copab
    #
    @3
    cB
    wcel
    #
    @0
    cS
    @3
    csn
    #
    cxp
    #
    wceq
    #
    wa
    #
    vy
    vx
    copab
    cF
    ccnv
    #
    vy
    cB
    @10
    cmpt
    @6
    @12
    vy
    vx
    @0
    cB
    cX
    csn
    #
    cmap
    co
    #
    wcel
    #
    @5
    wa
    #
    @8
    @0
    @14
    @9
    cxp
    #
    wceq
    #
    wa
    #
    @6
    @12
    @17
    @20
    @16
    @5
    @20
    @16
    @20
    @5
    @4
    cB
    wcel
    #
    @0
    @14
    @4
    csn
    #
    cxp
    #
    wceq
    #
    wa
    @16
    @21
    @24
    @16
    @14
    cB
    @0
    wf
    cX
    @14
    wcel
    #
    @21
    @0
    cB
    @14
    elmapi
    cX
    mapsncnv.x
    snid
    #
    @14
    cB
    cX
    @0
    ffvelrn
    sylancl
    cB
    @14
    @0
    cX
    @14
    eqid
    mapsncnv.b
    mapsncnv.x
    mapsnconst
    jca
    @5
    @8
    @21
    @19
    @24
    @3
    @4
    cB
    eleq1
    @5
    @18
    @23
    @0
    @5
    @9
    @22
    @14
    @3
    @4
    sneq
    xpeq2d
    eqeq2d
    anbi12d
    syl5ibrcom
    imp
    @8
    @19
    @17
    @8
    @17
    @19
    @18
    @15
    wcel
    #
    @3
    cX
    @18
    cfv
    #
    wceq
    #
    wa
    @8
    @27
    @29
    @8
    @14
    cB
    @18
    wf
    @27
    @14
    @3
    cB
    fconst6g
    cB
    @14
    @18
    mapsncnv.b
    cX
    snex
    elmap
    sylibr
    @8
    @28
    @3
    @25
    @28
    @3
    wceq
    @8
    @26
    @14
    @3
    cX
    vy
    vex
    fvconst2
    mp1i
    eqcomd
    jca
    @19
    @16
    @27
    @5
    @29
    @0
    @18
    @15
    eleq1
    @19
    @4
    @28
    @3
    cX
    @0
    @18
    fveq1
    eqeq2d
    anbi12d
    syl5ibrcom
    imp
    impbii
    @2
    @16
    @5
    @1
    @15
    @0
    cS
    @14
    cB
    cmap
    mapsncnv.s
    oveq2i
    eleq2i
    anbi1i
    @11
    @19
    @8
    @10
    @18
    @0
    cS
    @14
    @9
    mapsncnv.s
    xpeq1i
    eqeq2i
    anbi2i
    3bitr4i
    opabbii
    @13
    @6
    vx
    vy
    copab
    #
    ccnv
    @7
    cF
    @30
    cF
    vx
    @1
    @4
    cmpt
    @30
    mapsncnv.f
    vx
    vy
    @1
    @4
    df-mpt
    eqtri
    cnveqi
    @6
    vx
    vy
    cnvopab
    eqtri
    vy
    vx
    cB
    @10
    df-mpt
    3eqtr4i
end
