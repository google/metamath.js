include "wcel.mm"
include "w3a.mm"
include "ccnv.mm"
include "ccom.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "csymg.mm"
include "cfv.mm"
include "cminusg.mm"
include "eqid.mm"
include "symginv.mm"
include "3ad2ant2.mm"
include "cgrp.mm"
include "symggrp.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "simp3.mm"
include "wa.mm"
include "cplusg.mm"
include "co.mm"
include "symgov.mm"
include "symgcl.mm"
include "cid.mm"
include "cres.mm"
include "coass.mm"
include "wf1o.mm"
include "symgbasf1o.mm"
include "f1ococnv2.mm"
include "3syl.mm"
include "coeq1d.mm"
include "syl5eqr.mm"
include "wf.mm"
include "f1of.mm"
include "fcoi2.mm"
include "syl.mm"
include "eqtr2d.mm"
include "simpr.mm"
include "coeq2d.mm"
include "a1i.mm"
include "f1ococnv1.mm"
include "ad2antrr.mm"
include "eqtr3d.mm"
include "simplr.mm"
include "3eqtrrd.mm"
include "ex.mm"
include "ralrimiva.mm"
include "eqidd.mm"
include "coeq2.mm"
include "eqeq12d.mm"
include "eqreu.mm"
include "syl3anc.mm"

theorem symgfcoeu
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cG: class G
  let cV: class V
  let vp: setvar p
  assume symgfcoeu.g: |- G = ( Base ` ( SymGrp ` D ) )

  disjoint D p
  disjoint G p
  disjoint P p
  disjoint Q p
  disjoint V p
  assert |- ( ( D e. V /\ P e. G /\ Q e. G ) -> E! p e. G Q = ( P o. p ) )

  proof
    cD
    cV
    wcel
    #
    cP
    cG
    wcel
    #
    cQ
    cG
    wcel
    #
    w3a
    #
    cP
    ccnv
    #
    cQ
    ccom
    #
    cG
    wcel
    #
    cQ
    cP
    @5
    ccom
    #
    wceq
    #
    cQ
    cP
    vp
    cv
    #
    ccom
    #
    wceq
    #
    @9
    @5
    wceq
    #
    wi
    #
    vp
    cG
    wral
    @11
    vp
    cG
    wreu
    @3
    @4
    cG
    wcel
    #
    @2
    @6
    @3
    cP
    cD
    csymg
    cfv
    #
    cminusg
    cfv
    #
    cfv
    #
    @4
    cG
    @1
    @0
    @17
    @4
    wceq
    @2
    cD
    cG
    cP
    @15
    @16
    @15
    eqid
    #
    symgfcoeu.g
    @16
    eqid
    #
    symginv
    3ad2ant2
    @3
    @15
    cgrp
    wcel
    #
    @1
    @17
    cG
    wcel
    @0
    @1
    @20
    @2
    cD
    @15
    cV
    @18
    symggrp
    3ad2ant1
    @0
    @1
    @2
    simp2
    #
    cG
    @15
    @16
    cP
    symgfcoeu.g
    @19
    grpinvcl
    syl2anc
    eqeltrrd
    @0
    @1
    @2
    simp3
    #
    @14
    @2
    wa
    @4
    cQ
    @15
    cplusg
    cfv
    #
    co
    @5
    cG
    cD
    cG
    @23
    @15
    @4
    cQ
    @18
    symgfcoeu.g
    @23
    eqid
    #
    symgov
    cD
    cG
    @23
    @15
    @4
    cQ
    @18
    symgfcoeu.g
    @24
    symgcl
    eqeltrrd
    syl2anc
    @3
    @7
    cid
    cD
    cres
    #
    cQ
    ccom
    #
    cQ
    @3
    @7
    cP
    @4
    ccom
    #
    cQ
    ccom
    @26
    cP
    @4
    cQ
    coass
    @3
    @27
    @25
    cQ
    @3
    @1
    cD
    cD
    cP
    wf1o
    #
    @27
    @25
    wceq
    @21
    cD
    cG
    cP
    @15
    @18
    symgfcoeu.g
    symgbasf1o
    #
    cD
    cD
    cP
    f1ococnv2
    3syl
    coeq1d
    syl5eqr
    @3
    cD
    cD
    cQ
    wf
    #
    @26
    cQ
    wceq
    @3
    @2
    cD
    cD
    cQ
    wf1o
    @30
    @22
    cD
    cG
    cQ
    @15
    @18
    symgfcoeu.g
    symgbasf1o
    cD
    cD
    cQ
    f1of
    3syl
    cD
    cD
    cQ
    fcoi2
    syl
    eqtr2d
    @3
    @13
    vp
    cG
    @3
    @9
    cG
    wcel
    #
    wa
    #
    @11
    @12
    @32
    @11
    wa
    #
    @5
    @4
    @10
    ccom
    #
    @25
    @9
    ccom
    #
    @9
    @33
    cQ
    @10
    @4
    @32
    @11
    simpr
    coeq2d
    @33
    @4
    cP
    ccom
    #
    @9
    ccom
    #
    @34
    @35
    @37
    @34
    wceq
    @33
    @4
    cP
    @9
    coass
    a1i
    @3
    @37
    @35
    wceq
    @31
    @11
    @3
    @36
    @25
    @9
    @3
    @1
    @28
    @36
    @25
    wceq
    @21
    @29
    cD
    cD
    cP
    f1ococnv1
    3syl
    coeq1d
    ad2antrr
    eqtr3d
    @33
    cD
    cD
    @9
    wf
    #
    @35
    @9
    wceq
    @33
    @31
    cD
    cD
    @9
    wf1o
    @38
    @3
    @31
    @11
    simplr
    cD
    cG
    @9
    @15
    @18
    symgfcoeu.g
    symgbasf1o
    cD
    cD
    @9
    f1of
    3syl
    cD
    cD
    @9
    fcoi2
    syl
    3eqtrrd
    ex
    ralrimiva
    @11
    @8
    vp
    cG
    @5
    @12
    cQ
    cQ
    @10
    @7
    @12
    cQ
    eqidd
    @9
    @5
    cP
    coeq2
    eqeq12d
    eqreu
    syl3anc
end
