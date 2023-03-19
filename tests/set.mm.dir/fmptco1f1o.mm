include "wf1o.mm"
include "ccnv.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "wcel.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "adantr.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "elmapi.mm"
include "syl.mm"
include "f1of.mm"
include "fco.mm"
include "syl2anc.mm"
include "elmapg.mm"
include "biimpar.mm"
include "syl21anc.mm"
include "syl6eleqr.mm"
include "f1ocnv.mm"
include "3syl.mm"
include "wb.mm"
include "coass.mm"
include "cid.mm"
include "cres.mm"
include "ad2antrr.mm"
include "f1ococnv1.mm"
include "coeq2d.mm"
include "adantlr.mm"
include "fcoi1.mm"
include "eqtrd.mm"
include "syl5req.mm"
include "eqeq1d.mm"
include "eqcom.mm"
include "wfo.mm"
include "wfn.mm"
include "f1ofo.mm"
include "simplr.mm"
include "elmapfn.mm"
include "cocan2.mm"
include "syl3anc.mm"
include "3bitrrd.mm"
include "anasss.mm"
include "f1o3d.mm"
include "simpld.mm"

theorem fmptco1f1o
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cT: class T
  let vf: setvar f
  let cE: class E
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let vg: setvar g
  assume fmptco1f1o.a: |- A = ( R ^m E )
  assume fmptco1f1o.b: |- B = ( R ^m D )
  assume fmptco1f1o.f: |- F = ( f e. A |-> ( f o. T ) )
  assume fmptco1f1o.d: |- ( ph -> D e. V )
  assume fmptco1f1o.e: |- ( ph -> E e. W )
  assume fmptco1f1o.r: |- ( ph -> R e. X )
  assume fmptco1f1o.t: |- ( ph -> T : D -1-1-onto-> E )

  disjoint A f
  disjoint B f
  disjoint T f
  disjoint f ph
  disjoint A g
  disjoint f g
  disjoint B g
  disjoint T g
  disjoint g ph
  assert |- ( ph -> F : A -1-1-onto-> B )

  proof
    wph
    cA
    cB
    cF
    wf1o
    cF
    ccnv
    vg
    cB
    vg
    cv
    #
    cT
    ccnv
    #
    ccom
    #
    cmpt
    wceq
    wph
    vf
    vg
    cA
    cB
    vf
    cv
    #
    cT
    ccom
    #
    @2
    cF
    cF
    vf
    cA
    @4
    cmpt
    wceq
    wph
    fmptco1f1o.f
    a1i
    wph
    @3
    cA
    wcel
    #
    wa
    #
    @4
    cR
    cD
    cmap
    co
    #
    cB
    @6
    cR
    cX
    wcel
    #
    cD
    cV
    wcel
    #
    cD
    cR
    @4
    wf
    #
    @4
    @7
    wcel
    #
    wph
    @8
    @5
    fmptco1f1o.r
    adantr
    wph
    @9
    @5
    fmptco1f1o.d
    adantr
    @6
    cE
    cR
    @3
    wf
    #
    cD
    cE
    cT
    wf
    #
    @10
    @6
    @3
    cR
    cE
    cmap
    co
    #
    wcel
    #
    @12
    @6
    @3
    cA
    @14
    wph
    @5
    simpr
    fmptco1f1o.a
    syl6eleq
    @3
    cR
    cE
    elmapi
    syl
    wph
    @13
    @5
    wph
    cD
    cE
    cT
    wf1o
    #
    @13
    fmptco1f1o.t
    cD
    cE
    cT
    f1of
    syl
    adantr
    cD
    cE
    cR
    @3
    cT
    fco
    syl2anc
    @8
    @9
    wa
    @11
    @10
    cR
    cD
    @4
    cX
    cV
    elmapg
    biimpar
    syl21anc
    fmptco1f1o.b
    syl6eleqr
    wph
    @0
    cB
    wcel
    #
    wa
    #
    @2
    @14
    cA
    @18
    @8
    cE
    cW
    wcel
    #
    cE
    cR
    @2
    wf
    #
    @2
    @14
    wcel
    #
    wph
    @8
    @17
    fmptco1f1o.r
    adantr
    wph
    @19
    @17
    fmptco1f1o.e
    adantr
    @18
    cD
    cR
    @0
    wf
    #
    cE
    cD
    @1
    wf
    #
    @20
    @18
    @0
    @7
    wcel
    @22
    @18
    @0
    cB
    @7
    wph
    @17
    simpr
    fmptco1f1o.b
    syl6eleq
    @0
    cR
    cD
    elmapi
    syl
    #
    wph
    @23
    @17
    wph
    @16
    cE
    cD
    @1
    wf1o
    @23
    fmptco1f1o.t
    cD
    cE
    cT
    f1ocnv
    cE
    cD
    @1
    f1of
    3syl
    adantr
    cE
    cD
    cR
    @0
    @1
    fco
    syl2anc
    @8
    @19
    wa
    @21
    @20
    cR
    cE
    @2
    cX
    cW
    elmapg
    biimpar
    syl21anc
    #
    fmptco1f1o.a
    syl6eleqr
    wph
    @5
    @17
    @3
    @2
    wceq
    #
    @0
    @4
    wceq
    #
    wb
    @6
    @17
    wa
    #
    @27
    @2
    cT
    ccom
    #
    @4
    wceq
    #
    @4
    @29
    wceq
    #
    @26
    @28
    @0
    @29
    @4
    @28
    @29
    @0
    @1
    cT
    ccom
    #
    ccom
    #
    @0
    @0
    @1
    cT
    coass
    @28
    @33
    @0
    cid
    cD
    cres
    #
    ccom
    #
    @0
    @28
    @16
    @33
    @35
    wceq
    wph
    @16
    @5
    @17
    fmptco1f1o.t
    ad2antrr
    #
    @16
    @32
    @34
    @0
    cD
    cE
    cT
    f1ococnv1
    coeq2d
    syl
    @28
    @22
    @35
    @0
    wceq
    wph
    @17
    @22
    @5
    @24
    adantlr
    cD
    cR
    @0
    fcoi1
    syl
    eqtrd
    syl5req
    eqeq1d
    @30
    @31
    wb
    @28
    @29
    @4
    eqcom
    a1i
    @28
    cD
    cE
    cT
    wfo
    #
    @3
    cE
    wfn
    #
    @2
    cE
    wfn
    #
    @31
    @26
    wb
    @28
    @16
    @37
    @36
    cD
    cE
    cT
    f1ofo
    syl
    @28
    @15
    @38
    @28
    @3
    cA
    @14
    wph
    @5
    @17
    simplr
    fmptco1f1o.a
    syl6eleq
    @3
    cR
    cE
    elmapfn
    syl
    wph
    @17
    @39
    @5
    @18
    @21
    @39
    @25
    @2
    cR
    cE
    elmapfn
    syl
    adantlr
    cD
    cE
    cT
    @3
    @2
    cocan2
    syl3anc
    3bitrrd
    anasss
    f1o3d
    simpld
end
