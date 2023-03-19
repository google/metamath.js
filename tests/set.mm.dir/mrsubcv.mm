include "wf.mm"
include "wss.mm"
include "cun.mm"
include "wcel.mm"
include "w3a.mm"
include "cs1.mm"
include "cfv.mm"
include "cfrmd.mm"
include "cv.mm"
include "cif.mm"
include "cmpt.mm"
include "ccom.mm"
include "cgsu.mm"
include "co.mm"
include "wceq.mm"
include "cword.mm"
include "simp3.mm"
include "s1cld.mm"
include "cvv.mm"
include "wo.mm"
include "elun.mm"
include "cmcn.mm"
include "elfvex.mm"
include "eleq2s.mm"
include "cmvar.mm"
include "jaoi.mm"
include "sylbi.mm"
include "3ad2ant3.mm"
include "mrexval.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "eqid.mm"
include "mrsubval.mm"
include "syld3an3.mm"
include "wa.mm"
include "simpl1.mm"
include "ffvelrnda.mm"
include "ad2antrr.mm"
include "eleqtrd.mm"
include "wn.mm"
include "simplr.mm"
include "ifclda.mm"
include "fmptd.mm"
include "s1co.mm"
include "syl2anc.mm"
include "eleq1.mm"
include "fveq2.mm"
include "s1eq.mm"
include "ifbieq12d.mm"
include "fvex.mm"
include "s1cli.mm"
include "elexi.mm"
include "ifex.mm"
include "fvmpt.mm"
include "s1eqd.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "ffvelrnd.mm"
include "eqeltrrd.mm"
include "cbs.mm"
include "eqeltri.mm"
include "unex.mm"
include "frmdbas.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "gsumws1.mm"
include "3eqtrd.mm"

theorem mrsubcv
  let cA: class A
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cV: class V
  let cX: class X
  let ve: setvar e
  let vf: setvar f
  let vv: setvar v
  let vt: setvar t
  let cG: class G
  assume mrsubffval.c: |- C = ( mCN ` T )
  assume mrsubffval.v: |- V = ( mVR ` T )
  assume mrsubffval.r: |- R = ( mREx ` T )
  assume mrsubffval.s: |- S = ( mRSubst ` T )


  assert |- ( ( F : A --> R /\ A C_ V /\ X e. ( C u. V ) ) -> ( ( S ` F ) ` <" X "> ) = if ( X e. A , ( F ` X ) , <" X "> ) )

  proof
    cA
    cR
    cF
    wf
    #
    cA
    cV
    wss
    #
    cX
    cC
    cV
    cun
    #
    wcel
    #
    w3a
    #
    cX
    cs1
    #
    cF
    cS
    cfv
    cfv
    #
    @2
    cfrmd
    cfv
    #
    vv
    @2
    vv
    cv
    #
    cA
    wcel
    #
    @8
    cF
    cfv
    #
    @8
    cs1
    #
    cif
    #
    cmpt
    #
    @5
    ccom
    #
    cgsu
    co
    #
    @7
    cX
    cA
    wcel
    #
    cX
    cF
    cfv
    #
    @5
    cif
    #
    cs1
    #
    cgsu
    co
    #
    @18
    @0
    @1
    @3
    @5
    cR
    wcel
    @6
    @15
    wceq
    @4
    @5
    @2
    cword
    #
    cR
    @4
    cX
    @2
    @0
    @1
    @3
    simp3
    #
    s1cld
    @4
    cT
    cvv
    wcel
    #
    cR
    @21
    wceq
    #
    @3
    @0
    @23
    @1
    @3
    cX
    cC
    wcel
    #
    cX
    cV
    wcel
    #
    wo
    @23
    cX
    cC
    cV
    elun
    @25
    @23
    @26
    @23
    cX
    cT
    cmcn
    cfv
    #
    cC
    cX
    cT
    cmcn
    elfvex
    mrsubffval.c
    eleq2s
    @23
    cX
    cT
    cmvar
    cfv
    #
    cV
    cX
    cT
    cmvar
    elfvex
    mrsubffval.v
    eleq2s
    jaoi
    sylbi
    3ad2ant3
    cC
    cR
    cT
    cV
    cvv
    mrsubffval.c
    mrsubffval.v
    mrsubffval.r
    mrexval
    syl
    #
    eleqtrrd
    vv
    cA
    cC
    cR
    cS
    cT
    cF
    @7
    cV
    @5
    mrsubffval.c
    mrsubffval.v
    mrsubffval.r
    mrsubffval.s
    @7
    eqid
    #
    mrsubval
    syld3an3
    @4
    @14
    @19
    @7
    cgsu
    @4
    @14
    cX
    @13
    cfv
    #
    cs1
    #
    @19
    @4
    @3
    @2
    @21
    @13
    wf
    @14
    @32
    wceq
    @22
    @4
    vv
    @2
    @12
    @21
    @13
    @4
    @8
    @2
    wcel
    #
    wa
    #
    @9
    @10
    @11
    @21
    @34
    @9
    wa
    @10
    cR
    @21
    @34
    cA
    cR
    @8
    cF
    @0
    @1
    @3
    @33
    simpl1
    ffvelrnda
    @4
    @24
    @33
    @9
    @29
    ad2antrr
    eleqtrd
    @34
    @9
    wn
    #
    wa
    @8
    @2
    @4
    @33
    @35
    simplr
    s1cld
    ifclda
    @13
    eqid
    #
    fmptd
    #
    @2
    @21
    cX
    @13
    s1co
    syl2anc
    @4
    @31
    @18
    @3
    @0
    @31
    @18
    wceq
    @1
    vv
    cX
    @12
    @18
    @2
    @13
    @8
    cX
    wceq
    @9
    @16
    @10
    @11
    @17
    @5
    @8
    cX
    cA
    eleq1
    @8
    cX
    cF
    fveq2
    @8
    cX
    s1eq
    ifbieq12d
    @36
    @16
    @17
    @5
    cX
    cF
    fvex
    @5
    cvv
    cword
    cX
    s1cli
    elexi
    ifex
    fvmpt
    3ad2ant3
    #
    s1eqd
    eqtrd
    oveq2d
    @4
    @18
    @21
    wcel
    @20
    @18
    wceq
    @4
    @31
    @18
    @21
    @38
    @4
    @2
    @21
    cX
    @13
    @37
    @22
    ffvelrnd
    eqeltrrd
    @21
    @18
    @7
    @7
    cbs
    cfv
    #
    @21
    @2
    cvv
    wcel
    @39
    @21
    wceq
    cC
    cV
    cC
    @27
    cvv
    mrsubffval.c
    cT
    cmcn
    fvex
    eqeltri
    cV
    @28
    cvv
    mrsubffval.v
    cT
    cmvar
    fvex
    eqeltri
    unex
    @39
    @2
    @7
    cvv
    @30
    @39
    eqid
    frmdbas
    ax-mp
    eqcomi
    gsumws1
    syl
    3eqtrd
end
