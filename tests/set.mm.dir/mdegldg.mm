include "crg.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "csupp.mm"
include "co.mm"
include "cima.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "mdegval.mm"
include "3ad2ant2.mm"
include "cfn.mm"
include "c0.mm"
include "wss.mm"
include "wfun.mm"
include "cn0.mm"
include "cvv.mm"
include "wf.mm"
include "mplrcl.mm"
include "tdeglem1.mm"
include "syl.mm"
include "ffund.mm"
include "simp2.mm"
include "simp1.mm"
include "mplelsfi.mm"
include "fsuppimpd.mm"
include "imafi.mm"
include "syl2anc.mm"
include "csn.mm"
include "cxp.mm"
include "simp3.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "3ad2ant1.mm"
include "mpl0.mm"
include "neeqtrd.mm"
include "wfn.mm"
include "wb.mm"
include "cbs.mm"
include "eqid.mm"
include "mplelf.mm"
include "ffnd.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ccnv.mm"
include "cn.mm"
include "cmap.mm"
include "ovex.mm"
include "rabex2.mm"
include "fnsuppeq0.mm"
include "mp3an2.mm"
include "sylancl.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "cdm.mm"
include "suppssdm.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "fnimaeq0.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "syl5ss.mm"
include "cr.mm"
include "nn0ssre.mm"
include "ressxr.mm"
include "sstri.mm"
include "syl6ss.mm"
include "wor.mm"
include "xrltso.mm"
include "fisupcl.mm"
include "mpan.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "fvelimab.mm"
include "rexsupp.mm"
include "mp3an23.mm"
include "bitrd.mm"
include "mpbid.mm"

theorem mdegldg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let vh: setvar h
  let vm: setvar m
  let cF: class F
  let cH: class H
  let cI: class I
  let cY: class Y
  let c.0: class .0.
  let vf: setvar f
  let vi: setvar i
  let vr: setvar r
  let vy: setvar y
  let cG: class G
  assume mdegval.d: |- D = ( I mDeg R )
  assume mdegval.p: |- P = ( I mPoly R )
  assume mdegval.b: |- B = ( Base ` P )
  assume mdegval.z: |- .0. = ( 0g ` R )
  assume mdegval.a: |- A = { m e. ( NN0 ^m I ) | ( `' m " NN ) e. Fin }
  assume mdegval.h: |- H = ( h e. A |-> ( CCfld gsum h ) )
  assume mdegldg.y: |- Y = ( 0g ` P )

  disjoint A h
  disjoint I m
  disjoint .0. h
  disjoint A x
  disjoint B x
  disjoint F x
  disjoint H x
  disjoint I h
  disjoint R x
  disjoint .0. x
  disjoint h m
  disjoint D x
  disjoint B f
  disjoint B i
  disjoint B r
  disjoint f i
  disjoint f r
  disjoint i r
  disjoint I f
  disjoint I i
  disjoint I r
  disjoint R f
  disjoint R i
  disjoint R r
  disjoint .0. i
  disjoint .0. r
  disjoint h i
  disjoint h r
  disjoint f h
  disjoint F f
  disjoint H f
  disjoint .0. f
  disjoint A y
  disjoint x y
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint H y
  disjoint .0. y
  assert |- ( ( R e. Ring /\ F e. B /\ F =/= Y ) -> E. x e. A ( ( F ` x ) =/= .0. /\ ( H ` x ) = ( D ` F ) ) )

  proof
    cR
    crg
    wcel
    #
    cF
    cB
    wcel
    #
    cF
    cY
    wne
    #
    w3a
    #
    cF
    cD
    cfv
    #
    cH
    cF
    c.0
    csupp
    co
    #
    cima
    #
    wcel
    #
    vx
    cv
    #
    cF
    cfv
    c.0
    wne
    @8
    cH
    cfv
    @4
    wceq
    #
    wa
    vx
    cA
    wrex
    #
    @3
    @4
    @6
    cxr
    clt
    csup
    #
    @6
    @1
    @0
    @4
    @11
    wceq
    @2
    cA
    cB
    cD
    cP
    cR
    vh
    vm
    cF
    cH
    cI
    c.0
    mdegval.d
    mdegval.p
    mdegval.b
    mdegval.z
    mdegval.a
    mdegval.h
    mdegval
    3ad2ant2
    @3
    @6
    cfn
    wcel
    #
    @6
    c0
    wne
    #
    @6
    cxr
    wss
    #
    @11
    @6
    wcel
    #
    @3
    cH
    wfun
    @5
    cfn
    wcel
    @12
    @3
    cA
    cn0
    cH
    @3
    cI
    cvv
    wcel
    #
    cA
    cn0
    cH
    wf
    #
    @1
    @0
    @16
    @2
    cB
    cP
    cR
    cI
    cF
    mdegval.p
    mdegval.b
    mplrcl
    3ad2ant2
    #
    cA
    vh
    vm
    cH
    cI
    cvv
    mdegval.a
    mdegval.h
    tdeglem1
    syl
    #
    ffund
    @3
    cF
    c.0
    @3
    cB
    cP
    cR
    cF
    cI
    crg
    c.0
    mdegval.p
    mdegval.b
    mdegval.z
    @0
    @1
    @2
    simp2
    #
    @0
    @1
    @2
    simp1
    mplelsfi
    fsuppimpd
    cH
    @5
    imafi
    syl2anc
    @3
    @13
    @5
    c0
    wne
    #
    @3
    @21
    cF
    cA
    c.0
    csn
    cxp
    #
    wne
    @3
    cF
    cY
    @22
    @0
    @1
    @2
    simp3
    @3
    cA
    cP
    cR
    vm
    cI
    c.0
    cvv
    cY
    mdegval.p
    mdegval.a
    mdegval.z
    mdegldg.y
    @18
    @0
    @1
    cR
    cgrp
    wcel
    @2
    cR
    ringgrp
    3ad2ant1
    mpl0
    neeqtrd
    @3
    @5
    c0
    cF
    @22
    @3
    cF
    cA
    wfn
    #
    c.0
    cvv
    wcel
    #
    @5
    c0
    wceq
    #
    cF
    @22
    wceq
    wb
    #
    @3
    cA
    cR
    cbs
    cfv
    #
    cF
    @3
    cB
    cA
    cP
    cR
    vm
    cI
    @27
    cF
    mdegval.p
    @27
    eqid
    mdegval.b
    mdegval.a
    @20
    mplelf
    #
    ffnd
    #
    c.0
    cR
    c0g
    cfv
    cvv
    mdegval.z
    cR
    c0g
    fvex
    eqeltri
    #
    @23
    cA
    cvv
    wcel
    #
    @24
    @26
    vm
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vm
    cn0
    cI
    cmap
    co
    cA
    mdegval.a
    cn0
    cI
    cmap
    ovex
    rabex2
    #
    cA
    cF
    cvv
    cvv
    c.0
    fnsuppeq0
    mp3an2
    sylancl
    necon3bid
    mpbird
    @3
    @6
    c0
    @5
    c0
    @3
    cH
    cA
    wfn
    #
    @5
    cA
    wss
    #
    @6
    c0
    wceq
    @25
    wb
    @3
    cA
    cn0
    cH
    @19
    ffnd
    #
    @3
    cF
    cdm
    #
    @5
    cA
    cF
    c.0
    suppssdm
    @3
    cA
    @27
    cF
    wf
    @36
    cA
    wceq
    @28
    cA
    @27
    cF
    fdm
    syl
    syl5sseq
    #
    cA
    @5
    cH
    fnimaeq0
    syl2anc
    necon3bid
    mpbird
    @3
    @6
    cn0
    cxr
    @3
    @6
    cH
    crn
    #
    cn0
    cH
    @5
    imassrn
    @3
    @17
    @38
    cn0
    wss
    @19
    cA
    cn0
    cH
    frn
    syl
    syl5ss
    cn0
    cr
    cxr
    nn0ssre
    ressxr
    sstri
    syl6ss
    cxr
    clt
    wor
    @12
    @13
    @14
    w3a
    @15
    xrltso
    cxr
    @6
    clt
    fisupcl
    mpan
    syl3anc
    eqeltrd
    @3
    @7
    @9
    vx
    @5
    wrex
    #
    @10
    @3
    @33
    @34
    @7
    @39
    wb
    @35
    @37
    vx
    cA
    @5
    @4
    cH
    fvelimab
    syl2anc
    @3
    @23
    @39
    @10
    wb
    #
    @29
    @23
    @31
    @24
    @40
    @32
    @30
    @9
    vx
    cF
    cvv
    cvv
    cA
    c.0
    rexsupp
    mp3an23
    syl
    bitrd
    mpbid
end
