include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "csn.mm"
include "cfv.mm"
include "ccnv.mm"
include "cbs.mm"
include "cp0.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "crn.mm"
include "wf1o.mm"
include "clss.mm"
include "wf1.mm"
include "eqid.mm"
include "dihf11.mm"
include "3ad2ant1.mm"
include "f1f1orn.mm"
include "syl.mm"
include "dihlsprn.mm"
include "3adant3.mm"
include "f1ocnvdm.mm"
include "syl2anc.mm"
include "fveq2.mm"
include "dihcnvid2.mm"
include "syldan.mm"
include "dih0.mm"
include "adantr.mm"
include "eqeq12d.mm"
include "clmod.mm"
include "wb.mm"
include "id.mm"
include "dvhlmod.mm"
include "lspsneq0.mm"
include "sylan.mm"
include "bitrd.mm"
include "syl5ib.mm"
include "necon3d.mm"
include "3impia.mm"
include "wss.mm"
include "clvec.mm"
include "simpll1.mm"
include "dvhlvec.mm"
include "simplr.mm"
include "dihlss.mm"
include "simpll2.mm"
include "simpr.mm"
include "lspsnat.mm"
include "syl31anc.mm"
include "ex.mm"
include "simp1.mm"
include "sseq2d.mm"
include "simpl1.mm"
include "dihord.mm"
include "syl3anc.mm"
include "bitr3d.mm"
include "eqeq2d.mm"
include "dih11.mm"
include "cops.mm"
include "simpl1l.mm"
include "hlop.mm"
include "op0cl.mm"
include "3syl.mm"
include "orbi12d.mm"
include "3imtr3d.mm"
include "ralrimiva.mm"
include "cal.mm"
include "simp1l.mm"
include "hlatl.mm"
include "isat3.mm"
include "mpbir3and.mm"

theorem dihlspsnat
  let cA: class A
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  assume dihlspsnat.a: |- A = ( Atoms ` K )
  assume dihlspsnat.h: |- H = ( LHyp ` K )
  assume dihlspsnat.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihlspsnat.v: |- V = ( Base ` U )
  assume dihlspsnat.o: |- .0. = ( 0g ` U )
  assume dihlspsnat.n: |- N = ( LSpan ` U )
  assume dihlspsnat.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. V /\ X =/= .0. ) -> ( `' I ` ( N ` { X } ) ) e. A )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cX
    cV
    wcel
    #
    cX
    c.0
    wne
    #
    w3a
    #
    cX
    csn
    cN
    cfv
    #
    cI
    ccnv
    cfv
    #
    cA
    wcel
    #
    @7
    cK
    cbs
    cfv
    #
    wcel
    #
    @7
    cK
    cp0
    cfv
    #
    wne
    #
    vx
    cv
    #
    @7
    cK
    cple
    cfv
    #
    wbr
    #
    @13
    @7
    wceq
    #
    @13
    @11
    wceq
    #
    wo
    #
    wi
    #
    vx
    @9
    wral
    #
    @5
    @9
    cI
    crn
    #
    cI
    wf1o
    #
    @6
    @21
    wcel
    #
    @10
    @5
    @9
    cU
    clss
    cfv
    #
    cI
    wf1
    #
    @22
    @2
    @3
    @25
    @4
    @9
    @24
    cU
    cH
    cI
    cK
    cW
    @9
    eqid
    #
    dihlspsnat.h
    dihlspsnat.i
    dihlspsnat.u
    @24
    eqid
    #
    dihf11
    3ad2ant1
    @9
    @24
    cI
    f1f1orn
    syl
    @2
    @3
    @23
    @4
    cU
    cH
    cI
    cK
    cN
    cV
    cW
    cX
    dihlspsnat.h
    dihlspsnat.u
    dihlspsnat.v
    dihlspsnat.n
    dihlspsnat.i
    dihlsprn
    #
    3adant3
    #
    @9
    @21
    @6
    cI
    f1ocnvdm
    syl2anc
    #
    @2
    @3
    @4
    @12
    @2
    @3
    wa
    #
    @7
    @11
    cX
    c.0
    @7
    @11
    wceq
    @7
    cI
    cfv
    #
    @11
    cI
    cfv
    #
    wceq
    #
    @31
    cX
    c.0
    wceq
    #
    @7
    @11
    cI
    fveq2
    @31
    @34
    @6
    c.0
    csn
    #
    wceq
    #
    @35
    @31
    @32
    @6
    @33
    @36
    @2
    @3
    @23
    @32
    @6
    wceq
    #
    @28
    cH
    cI
    cK
    cW
    @6
    dihlspsnat.h
    dihlspsnat.i
    dihcnvid2
    #
    syldan
    @2
    @33
    @36
    wceq
    #
    @3
    cU
    cH
    cI
    cK
    c.0
    cW
    @11
    @11
    eqid
    #
    dihlspsnat.h
    dihlspsnat.i
    dihlspsnat.u
    dihlspsnat.o
    dih0
    #
    adantr
    eqeq12d
    @2
    cU
    clmod
    wcel
    @3
    @37
    @35
    wb
    @2
    cU
    cH
    cK
    cW
    dihlspsnat.h
    dihlspsnat.u
    @2
    id
    dvhlmod
    cN
    cV
    cU
    cX
    c.0
    dihlspsnat.v
    dihlspsnat.o
    dihlspsnat.n
    lspsneq0
    sylan
    bitrd
    syl5ib
    necon3d
    3impia
    @5
    @19
    vx
    @9
    @5
    @13
    @9
    wcel
    #
    wa
    #
    @13
    cI
    cfv
    #
    @6
    wss
    #
    @45
    @6
    wceq
    #
    @45
    @36
    wceq
    #
    wo
    #
    @15
    @18
    @44
    @46
    @49
    @44
    @46
    wa
    #
    cU
    clvec
    wcel
    @45
    @24
    wcel
    #
    @3
    @46
    @49
    @50
    cU
    cH
    cK
    cW
    dihlspsnat.h
    dihlspsnat.u
    @2
    @3
    @4
    @43
    @46
    simpll1
    #
    dvhlvec
    @50
    @2
    @43
    @51
    @52
    @5
    @43
    @46
    simplr
    @9
    @24
    cU
    cH
    cI
    cK
    cW
    @13
    @26
    dihlspsnat.h
    dihlspsnat.i
    dihlspsnat.u
    @27
    dihlss
    syl2anc
    @2
    @3
    @4
    @43
    @46
    simpll2
    @44
    @46
    simpr
    @24
    @45
    cN
    cV
    cU
    cX
    c.0
    dihlspsnat.v
    dihlspsnat.o
    @27
    dihlspsnat.n
    lspsnat
    syl31anc
    ex
    @44
    @45
    @32
    wss
    #
    @46
    @15
    @44
    @32
    @6
    @45
    @5
    @38
    @43
    @5
    @2
    @23
    @38
    @2
    @3
    @4
    simp1
    @29
    @39
    syl2anc
    adantr
    #
    sseq2d
    @44
    @2
    @43
    @10
    @53
    @15
    wb
    @2
    @3
    @4
    @43
    simpl1
    #
    @5
    @43
    simpr
    #
    @5
    @10
    @43
    @30
    adantr
    #
    @9
    cH
    cI
    cK
    @14
    cW
    @13
    @7
    @26
    @14
    eqid
    #
    dihlspsnat.h
    dihlspsnat.i
    dihord
    syl3anc
    bitr3d
    @44
    @47
    @16
    @48
    @17
    @44
    @45
    @32
    wceq
    #
    @47
    @16
    @44
    @32
    @6
    @45
    @54
    eqeq2d
    @44
    @2
    @43
    @10
    @59
    @16
    wb
    @55
    @56
    @57
    @9
    cH
    cI
    cK
    cW
    @13
    @7
    @26
    dihlspsnat.h
    dihlspsnat.i
    dih11
    syl3anc
    bitr3d
    @44
    @45
    @33
    wceq
    #
    @48
    @17
    @44
    @33
    @36
    @45
    @44
    @2
    @40
    @55
    @42
    syl
    eqeq2d
    @44
    @2
    @43
    @11
    @9
    wcel
    #
    @60
    @17
    wb
    @55
    @56
    @44
    @0
    cK
    cops
    wcel
    @61
    @0
    @1
    @3
    @4
    @43
    simpl1l
    cK
    hlop
    @9
    cK
    @11
    @26
    @41
    op0cl
    3syl
    @9
    cH
    cI
    cK
    cW
    @13
    @11
    @26
    dihlspsnat.h
    dihlspsnat.i
    dih11
    syl3anc
    bitr3d
    orbi12d
    3imtr3d
    ralrimiva
    @5
    @0
    cK
    cal
    wcel
    @8
    @10
    @12
    @20
    w3a
    wb
    @0
    @1
    @3
    @4
    simp1l
    cK
    hlatl
    vx
    cA
    @9
    @7
    cK
    @14
    @11
    @26
    @58
    @41
    dihlspsnat.a
    isat3
    3syl
    mpbir3and
end
