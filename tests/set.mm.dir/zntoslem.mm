include "cn0.mm"
include "wcel.mm"
include "cpo.mm"
include "cv.mm"
include "wbr.mm"
include "wo.mm"
include "wral.mm"
include "ctos.mm"
include "cvv.mm"
include "czn.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "cbs.mm"
include "wceq.mm"
include "cple.mm"
include "wa.mm"
include "ccnv.mm"
include "cle.mm"
include "cr.mm"
include "wf.mm"
include "wss.mm"
include "wf1o.mm"
include "znf1o.mm"
include "f1ocnv.mm"
include "syl.mm"
include "f1of.mm"
include "cz.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cif.mm"
include "sseq1.mm"
include "ssid.mm"
include "elfzoelz.mm"
include "ssriv.mm"
include "keephyp.mm"
include "eqsstri.mm"
include "zssre.mm"
include "sstri.mm"
include "fss.mm"
include "sylancl.mm"
include "ffvelrnda.mm"
include "leidd.mm"
include "wb.mm"
include "znleval2.mm"
include "3anidm23.mm"
include "mpbird.mm"
include "w3a.mm"
include "3com23.mm"
include "anbi12d.mm"
include "3adant3.mm"
include "3adant2.mm"
include "letri3d.mm"
include "wf1.mm"
include "f1of1.mm"
include "f1fveq.mm"
include "sylan.mm"
include "3impb.mm"
include "3bitr2d.mm"
include "biimpd.mm"
include "wi.mm"
include "3ad2antr1.mm"
include "3ad2antr2.mm"
include "3ad2antr3.mm"
include "letr.mm"
include "syl3anc.mm"
include "3adant3r3.mm"
include "3adant3r1.mm"
include "3adant3r2.mm"
include "3imtr4d.mm"
include "isposd.mm"
include "letrid.mm"
include "orbi12d.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "istos.mm"
include "sylanbrc.mm"

theorem zntoslem
  let cF: class F
  let c.le: class .<_
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let cB: class B
  assume znle2.y: |- Y = ( Z/nZ ` N )
  assume znle2.f: |- F = ( ( ZRHom ` Y ) |` W )
  assume znle2.w: |- W = if ( N = 0 , ZZ , ( 0 ..^ N ) )
  assume znle2.l: |- .<_ = ( le ` Y )
  assume znleval.x: |- X = ( Base ` Y )


  assert |- ( N e. NN0 -> Y e. Toset )

  proof
    cN
    cn0
    wcel
    #
    cY
    cpo
    wcel
    vx
    cv
    #
    vy
    cv
    #
    c.le
    wbr
    #
    @2
    @1
    c.le
    wbr
    #
    wo
    #
    vy
    cX
    wral
    vx
    cX
    wral
    cY
    ctos
    wcel
    @0
    vx
    vy
    vz
    cX
    cY
    c.le
    cY
    cvv
    wcel
    @0
    cY
    cN
    czn
    cfv
    cvv
    znle2.y
    cN
    czn
    fvex
    eqeltri
    a1i
    cX
    cY
    cbs
    cfv
    wceq
    @0
    znleval.x
    a1i
    c.le
    cY
    cple
    cfv
    wceq
    @0
    znle2.l
    a1i
    @0
    @1
    cX
    wcel
    #
    wa
    #
    @1
    @1
    c.le
    wbr
    #
    @1
    cF
    ccnv
    #
    cfv
    #
    @10
    cle
    wbr
    #
    @7
    @10
    @0
    cX
    cr
    @1
    @9
    @0
    cX
    cW
    @9
    wf
    #
    cW
    cr
    wss
    cX
    cr
    @9
    wf
    @0
    cX
    cW
    @9
    wf1o
    #
    @12
    @0
    cW
    cX
    cF
    wf1o
    @13
    cX
    cF
    cN
    cW
    cY
    znle2.y
    znleval.x
    znle2.f
    znle2.w
    znf1o
    cW
    cX
    cF
    f1ocnv
    syl
    #
    cX
    cW
    @9
    f1of
    syl
    cW
    cz
    cr
    cW
    cN
    cc0
    wceq
    #
    cz
    cc0
    cN
    cfzo
    co
    #
    cif
    #
    cz
    znle2.w
    @15
    cz
    cz
    wss
    @16
    cz
    wss
    @17
    cz
    wss
    cz
    @16
    cz
    @17
    cz
    sseq1
    @16
    @17
    cz
    sseq1
    cz
    ssid
    vx
    @16
    cz
    @1
    cc0
    cN
    elfzoelz
    ssriv
    keephyp
    eqsstri
    zssre
    sstri
    cX
    cW
    cr
    @9
    fss
    sylancl
    #
    ffvelrnda
    #
    leidd
    @0
    @6
    @8
    @11
    wb
    @1
    @1
    cF
    c.le
    cN
    cW
    cX
    cY
    znle2.y
    znle2.f
    znle2.w
    znle2.l
    znleval.x
    znleval2
    3anidm23
    mpbird
    @0
    @6
    @2
    cX
    wcel
    #
    w3a
    #
    @3
    @4
    wa
    #
    @1
    @2
    wceq
    #
    @21
    @22
    @10
    @2
    @9
    cfv
    #
    cle
    wbr
    #
    @24
    @10
    cle
    wbr
    #
    wa
    @10
    @24
    wceq
    #
    @23
    @21
    @3
    @25
    @4
    @26
    @1
    @2
    cF
    c.le
    cN
    cW
    cX
    cY
    znle2.y
    znle2.f
    znle2.w
    znle2.l
    znleval.x
    znleval2
    #
    @0
    @20
    @6
    @4
    @26
    wb
    @2
    @1
    cF
    c.le
    cN
    cW
    cX
    cY
    znle2.y
    znle2.f
    znle2.w
    znle2.l
    znleval.x
    znleval2
    3com23
    #
    anbi12d
    @21
    @10
    @24
    @0
    @6
    @10
    cr
    wcel
    #
    @20
    @19
    3adant3
    #
    @0
    @20
    @24
    cr
    wcel
    #
    @6
    @0
    cX
    cr
    @2
    @9
    @18
    ffvelrnda
    #
    3adant2
    #
    letri3d
    @0
    @6
    @20
    @27
    @23
    wb
    #
    @0
    cX
    cW
    @9
    wf1
    #
    @6
    @20
    wa
    @35
    @0
    @13
    @36
    @14
    cX
    cW
    @9
    f1of1
    syl
    cX
    cW
    @1
    @2
    @9
    f1fveq
    sylan
    3impb
    3bitr2d
    biimpd
    @0
    @6
    @20
    vz
    cv
    #
    cX
    wcel
    #
    w3a
    wa
    #
    @25
    @24
    @37
    @9
    cfv
    #
    cle
    wbr
    #
    wa
    #
    @10
    @40
    cle
    wbr
    #
    @3
    @2
    @37
    c.le
    wbr
    #
    wa
    @1
    @37
    c.le
    wbr
    #
    @39
    @30
    @32
    @40
    cr
    wcel
    #
    @42
    @43
    wi
    @0
    @20
    @6
    @30
    @38
    @19
    3ad2antr1
    @0
    @6
    @20
    @32
    @38
    @33
    3ad2antr2
    @0
    @6
    @38
    @46
    @20
    @0
    cX
    cr
    @37
    @9
    @18
    ffvelrnda
    3ad2antr3
    @10
    @24
    @40
    letr
    syl3anc
    @39
    @3
    @25
    @44
    @41
    @0
    @6
    @20
    @3
    @25
    wb
    @38
    @28
    3adant3r3
    @0
    @20
    @38
    @44
    @41
    wb
    @6
    @2
    @37
    cF
    c.le
    cN
    cW
    cX
    cY
    znle2.y
    znle2.f
    znle2.w
    znle2.l
    znleval.x
    znleval2
    3adant3r1
    anbi12d
    @0
    @6
    @38
    @45
    @43
    wb
    @20
    @1
    @37
    cF
    c.le
    cN
    cW
    cX
    cY
    znle2.y
    znle2.f
    znle2.w
    znle2.l
    znleval.x
    znleval2
    3adant3r2
    3imtr4d
    isposd
    @0
    @5
    vx
    vy
    cX
    cX
    @0
    @6
    @20
    @5
    @21
    @5
    @25
    @26
    wo
    @21
    @10
    @24
    @31
    @34
    letrid
    @21
    @3
    @25
    @4
    @26
    @28
    @29
    orbi12d
    mpbird
    3expb
    ralrimivva
    vx
    vy
    cX
    cY
    c.le
    znleval.x
    znle2.l
    istos
    sylanbrc
end
