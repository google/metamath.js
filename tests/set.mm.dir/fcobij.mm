include "cmap.mm"
include "co.mm"
include "cv.mm"
include "ccom.mm"
include "ccnv.mm"
include "cmpt.mm"
include "eqid.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "wf1o.mm"
include "f1of.mm"
include "syl.mm"
include "adantr.mm"
include "elmapd.mm"
include "biimpa.mm"
include "fco.mm"
include "syl2anc.mm"
include "wb.mm"
include "mpbird.mm"
include "f1ocnv.mm"
include "3syl.mm"
include "wceq.mm"
include "cid.mm"
include "cres.mm"
include "simpr.mm"
include "coeq2d.mm"
include "coass.mm"
include "syl6eqr.mm"
include "simpll.mm"
include "f1ococnv2.mm"
include "coeq1d.mm"
include "simplrr.mm"
include "fcoi2.mm"
include "3eqtrrd.mm"
include "f1ococnv1.mm"
include "simplrl.mm"
include "impbida.mm"
include "f1o2d.mm"

theorem fcobij
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cG: class G
  let cV: class V
  let cW: class W
  let vh: setvar h
  assume fcobij.1: |- ( ph -> G : S -1-1-onto-> T )
  assume fcobij.2: |- ( ph -> R e. U )
  assume fcobij.3: |- ( ph -> S e. V )
  assume fcobij.4: |- ( ph -> T e. W )

  disjoint G f
  disjoint R f
  disjoint S f
  disjoint T f
  disjoint f ph
  disjoint f h
  disjoint G h
  disjoint R h
  disjoint S h
  disjoint T h
  disjoint h ph
  assert |- ( ph -> ( f e. ( S ^m R ) |-> ( G o. f ) ) : ( S ^m R ) -1-1-onto-> ( T ^m R ) )

  proof
    wph
    vf
    vh
    cS
    cR
    cmap
    co
    #
    cT
    cR
    cmap
    co
    #
    cG
    vf
    cv
    #
    ccom
    #
    cG
    ccnv
    #
    vh
    cv
    #
    ccom
    #
    vf
    @0
    @3
    cmpt
    #
    @7
    eqid
    wph
    @2
    @0
    wcel
    #
    wa
    #
    @3
    @1
    wcel
    #
    cR
    cT
    @3
    wf
    #
    @9
    cS
    cT
    cG
    wf
    #
    cR
    cS
    @2
    wf
    #
    @11
    wph
    @12
    @8
    wph
    cS
    cT
    cG
    wf1o
    #
    @12
    fcobij.1
    cS
    cT
    cG
    f1of
    syl
    adantr
    wph
    @8
    @13
    wph
    cS
    cR
    @2
    cV
    cU
    fcobij.3
    fcobij.2
    elmapd
    biimpa
    #
    cR
    cS
    cT
    cG
    @2
    fco
    syl2anc
    wph
    @10
    @11
    wb
    @8
    wph
    cT
    cR
    @3
    cW
    cU
    fcobij.4
    fcobij.2
    elmapd
    adantr
    mpbird
    wph
    @5
    @1
    wcel
    #
    wa
    #
    @6
    @0
    wcel
    #
    cR
    cS
    @6
    wf
    #
    @17
    cT
    cS
    @4
    wf
    #
    cR
    cT
    @5
    wf
    #
    @19
    wph
    @20
    @16
    wph
    @14
    cT
    cS
    @4
    wf1o
    @20
    fcobij.1
    cS
    cT
    cG
    f1ocnv
    cT
    cS
    @4
    f1of
    3syl
    adantr
    wph
    @16
    @21
    wph
    cT
    cR
    @5
    cW
    cU
    fcobij.4
    fcobij.2
    elmapd
    biimpa
    #
    cR
    cT
    cS
    @4
    @5
    fco
    syl2anc
    wph
    @18
    @19
    wb
    @16
    wph
    cS
    cR
    @6
    cV
    cU
    fcobij.3
    fcobij.2
    elmapd
    adantr
    mpbird
    wph
    @8
    @16
    wa
    #
    wa
    #
    @2
    @6
    wceq
    #
    @5
    @3
    wceq
    #
    @24
    @25
    wa
    #
    @3
    cG
    @4
    ccom
    #
    @5
    ccom
    #
    cid
    cT
    cres
    #
    @5
    ccom
    #
    @5
    @27
    @3
    cG
    @6
    ccom
    @29
    @27
    @2
    @6
    cG
    @24
    @25
    simpr
    coeq2d
    cG
    @4
    @5
    coass
    syl6eqr
    @27
    @28
    @30
    @5
    @27
    wph
    @14
    @28
    @30
    wceq
    wph
    @23
    @25
    simpll
    #
    fcobij.1
    cS
    cT
    cG
    f1ococnv2
    3syl
    coeq1d
    @27
    @21
    @31
    @5
    wceq
    @27
    wph
    @16
    @21
    @32
    wph
    @8
    @16
    @25
    simplrr
    @22
    syl2anc
    cR
    cT
    @5
    fcoi2
    syl
    3eqtrrd
    @24
    @26
    wa
    #
    @6
    @4
    cG
    ccom
    #
    @2
    ccom
    #
    cid
    cS
    cres
    #
    @2
    ccom
    #
    @2
    @33
    @6
    @4
    @3
    ccom
    @35
    @33
    @5
    @3
    @4
    @24
    @26
    simpr
    coeq2d
    @4
    cG
    @2
    coass
    syl6eqr
    @33
    @34
    @36
    @2
    @33
    wph
    @14
    @34
    @36
    wceq
    wph
    @23
    @26
    simpll
    #
    fcobij.1
    cS
    cT
    cG
    f1ococnv1
    3syl
    coeq1d
    @33
    @13
    @37
    @2
    wceq
    @33
    wph
    @8
    @13
    @38
    wph
    @8
    @16
    @26
    simplrl
    @15
    syl2anc
    cR
    cS
    @2
    fcoi2
    syl
    3eqtrrd
    impbida
    f1o2d
end
