include "wcel.mm"
include "cxr.mm"
include "wa.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "csupp.mm"
include "co.mm"
include "cima.mm"
include "clt.mm"
include "csup.mm"
include "cv.mm"
include "wral.mm"
include "wceq.mm"
include "wi.mm"
include "mdegval.mm"
include "adantr.mm"
include "breq1d.mm"
include "wss.mm"
include "wb.mm"
include "crn.mm"
include "imassrn.mm"
include "cn0.mm"
include "wf.mm"
include "cvv.mm"
include "mplrcl.mm"
include "tdeglem1.mm"
include "syl.mm"
include "frn.mm"
include "cr.mm"
include "nn0ssre.mm"
include "ressxr.mm"
include "sstri.mm"
include "syl6ss.mm"
include "syl5ss.mm"
include "supxrleub.mm"
include "sylancom.mm"
include "wfn.mm"
include "ffn.mm"
include "cdm.mm"
include "suppssdm.mm"
include "cbs.mm"
include "eqid.mm"
include "simpl.mm"
include "mplelf.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "breq1.mm"
include "ralima.mm"
include "syl2anc.mm"
include "csn.mm"
include "cdif.mm"
include "ccnv.mm"
include "cn.mm"
include "cfn.mm"
include "cmap.mm"
include "crab.mm"
include "ovex.mm"
include "rabex.mm"
include "a1i.mm"
include "syl5eqel.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "w3a.mm"
include "wne.mm"
include "elsuppfn.mm"
include "biantrur.mm"
include "eldifsn.mm"
include "bitr4i.mm"
include "anbi2d.mm"
include "bitrd.mm"
include "syl3anc.mm"
include "imbi1d.mm"
include "impexp.mm"
include "wn.mm"
include "con34b.mm"
include "simplr.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "xrltnle.mm"
include "bicomd.mm"
include "wo.mm"
include "ianor.mm"
include "xchnxbir.mm"
include "orcom.mm"
include "notnoti.mm"
include "biorfi.mm"
include "nne.mm"
include "3bitr2i.mm"
include "syl5bb.mm"
include "imbi12d.mm"
include "pm5.74da.mm"
include "ralbidv2.mm"
include "3bitrd.mm"

theorem mdegleb
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let vh: setvar h
  let vm: setvar m
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let c.0: class .0.
  let vf: setvar f
  let vi: setvar i
  let vr: setvar r
  let vy: setvar y
  assume mdegval.d: |- D = ( I mDeg R )
  assume mdegval.p: |- P = ( I mPoly R )
  assume mdegval.b: |- B = ( Base ` P )
  assume mdegval.z: |- .0. = ( 0g ` R )
  assume mdegval.a: |- A = { m e. ( NN0 ^m I ) | ( `' m " NN ) e. Fin }
  assume mdegval.h: |- H = ( h e. A |-> ( CCfld gsum h ) )

  disjoint A h
  disjoint I m
  disjoint .0. h
  disjoint A x
  disjoint B x
  disjoint F x
  disjoint G x
  disjoint H x
  disjoint I h
  disjoint R x
  disjoint .0. x
  disjoint h m
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
  disjoint G y
  disjoint H y
  disjoint .0. y
  assert |- ( ( F e. B /\ G e. RR* ) -> ( ( D ` F ) <_ G <-> A. x e. A ( G < ( H ` x ) -> ( F ` x ) = .0. ) ) )

  proof
    cF
    cB
    wcel
    #
    cG
    cxr
    wcel
    #
    wa
    #
    cF
    cD
    cfv
    #
    cG
    cle
    wbr
    cH
    cF
    c.0
    csupp
    co
    #
    cima
    #
    cxr
    clt
    csup
    #
    cG
    cle
    wbr
    #
    vy
    cv
    #
    cG
    cle
    wbr
    #
    vy
    @5
    wral
    #
    cG
    vx
    cv
    #
    cH
    cfv
    #
    clt
    wbr
    #
    @11
    cF
    cfv
    #
    c.0
    wceq
    #
    wi
    #
    vx
    cA
    wral
    #
    @2
    @3
    @6
    cG
    cle
    @0
    @3
    @6
    wceq
    @1
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
    adantr
    breq1d
    @0
    @1
    @5
    cxr
    wss
    @7
    @10
    wb
    @2
    @5
    cH
    crn
    #
    cxr
    cH
    @4
    imassrn
    @2
    @18
    cn0
    cxr
    @2
    cA
    cn0
    cH
    wf
    #
    @18
    cn0
    wss
    @2
    cI
    cvv
    wcel
    #
    @19
    @0
    @20
    @1
    cB
    cP
    cR
    cI
    cF
    mdegval.p
    mdegval.b
    mplrcl
    adantr
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
    cA
    cn0
    cH
    frn
    syl
    cn0
    cr
    cxr
    nn0ssre
    ressxr
    sstri
    #
    syl6ss
    syl5ss
    vy
    @5
    cG
    supxrleub
    sylancom
    @2
    @10
    @12
    cG
    cle
    wbr
    #
    vx
    @4
    wral
    #
    @17
    @2
    cH
    cA
    wfn
    #
    @4
    cA
    wss
    @10
    @24
    wb
    @2
    @19
    @25
    @21
    cA
    cn0
    cH
    ffn
    syl
    @2
    cF
    cdm
    #
    @4
    cA
    cF
    c.0
    suppssdm
    @2
    cA
    cR
    cbs
    cfv
    #
    cF
    wf
    #
    @26
    cA
    wceq
    @2
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
    @0
    @1
    simpl
    mplelf
    #
    cA
    @27
    cF
    fdm
    syl
    syl5sseq
    @9
    @23
    vy
    vx
    cA
    @4
    cH
    @8
    @12
    cG
    cle
    breq1
    ralima
    syl2anc
    @2
    @23
    @16
    vx
    @4
    cA
    @2
    @11
    @4
    wcel
    #
    @23
    wi
    @11
    cA
    wcel
    #
    @14
    cvv
    c.0
    csn
    cdif
    wcel
    #
    wa
    #
    @23
    wi
    #
    @31
    @16
    wi
    #
    @2
    @30
    @33
    @23
    @2
    cF
    cA
    wfn
    #
    cA
    cvv
    wcel
    #
    c.0
    cvv
    wcel
    #
    @30
    @33
    wb
    @2
    @28
    @36
    @29
    cA
    @27
    cF
    ffn
    syl
    @2
    cA
    vm
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    #
    vm
    cn0
    cI
    cmap
    co
    #
    crab
    #
    cvv
    mdegval.a
    @41
    cvv
    wcel
    @2
    @39
    vm
    @40
    cn0
    cI
    cmap
    ovex
    rabex
    a1i
    syl5eqel
    @38
    @2
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
    a1i
    @36
    @37
    @38
    w3a
    #
    @30
    @31
    @14
    c.0
    wne
    #
    wa
    @33
    @11
    cF
    cvv
    cvv
    cA
    c.0
    elsuppfn
    @42
    @43
    @32
    @31
    @43
    @32
    wb
    @42
    @43
    @14
    cvv
    wcel
    #
    @43
    wa
    #
    @32
    @44
    @43
    @11
    cF
    fvex
    #
    biantrur
    @14
    cvv
    c.0
    eldifsn
    #
    bitr4i
    a1i
    anbi2d
    bitrd
    syl3anc
    imbi1d
    @34
    @31
    @32
    @23
    wi
    #
    wi
    @2
    @35
    @31
    @32
    @23
    impexp
    @2
    @31
    @48
    @16
    @48
    @23
    wn
    #
    @32
    wn
    #
    wi
    @2
    @31
    wa
    #
    @16
    @32
    @23
    con34b
    @51
    @49
    @13
    @50
    @15
    @51
    @13
    @49
    @51
    @1
    @12
    cxr
    wcel
    @13
    @49
    wb
    @0
    @1
    @31
    simplr
    @51
    cn0
    cxr
    @12
    @22
    @2
    cA
    cn0
    @11
    cH
    @21
    ffvelrnda
    sseldi
    cG
    @12
    xrltnle
    syl2anc
    bicomd
    @50
    @44
    wn
    #
    @43
    wn
    #
    wo
    #
    @51
    @15
    @45
    @54
    @32
    @44
    @43
    ianor
    @47
    xchnxbir
    @54
    @15
    wb
    @51
    @54
    @53
    @52
    wo
    @53
    @15
    @52
    @53
    orcom
    @52
    @53
    @44
    @46
    notnoti
    biorfi
    @14
    c.0
    nne
    3bitr2i
    a1i
    syl5bb
    imbi12d
    syl5bb
    pm5.74da
    syl5bb
    bitrd
    ralbidv2
    bitrd
    3bitrd
end
