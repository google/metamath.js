include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wpss.mm"
include "wrex.mm"
include "wn.mm"
include "copab.mm"
include "wbr.mm"
include "wb.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "psseq1.mm"
include "rexbidv.mm"
include "notbid.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "psseq2.mm"
include "eqid.mm"
include "brabg.mm"
include "syl2anc.mm"
include "lcvfbr.mm"
include "breqd.mm"
include "jca.mm"
include "biantrurd.mm"
include "3bitr4d.mm"

theorem lcvbr
  let wph: wff ph
  let cC: class C
  let cS: class S
  let cT: class T
  let cU: class U
  let cW: class W
  let cX: class X
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  assume lcvfbr.s: |- S = ( LSubSp ` W )
  assume lcvfbr.c: |- C = ( <oL ` W )
  assume lcvfbr.w: |- ( ph -> W e. X )
  assume lcvfbr.t: |- ( ph -> T e. S )
  assume lcvfbr.u: |- ( ph -> U e. S )

  disjoint S s
  disjoint W s
  disjoint T s
  disjoint U s
  disjoint s t
  disjoint s u
  disjoint s w
  disjoint t u
  disjoint t w
  disjoint S t
  disjoint u w
  disjoint S u
  disjoint S w
  disjoint W t
  disjoint W u
  disjoint W w
  disjoint T t
  disjoint T u
  disjoint U t
  disjoint U u
  assert |- ( ph -> ( T C U <-> ( T C. U /\ -. E. s e. S ( T C. s /\ s C. U ) ) ) )

  proof
    wph
    cT
    cU
    vt
    cv
    #
    cS
    wcel
    #
    vu
    cv
    #
    cS
    wcel
    #
    wa
    #
    @0
    @2
    wpss
    #
    @0
    vs
    cv
    #
    wpss
    #
    @6
    @2
    wpss
    #
    wa
    #
    vs
    cS
    wrex
    #
    wn
    #
    wa
    #
    wa
    #
    vt
    vu
    copab
    #
    wbr
    #
    cT
    cS
    wcel
    #
    cU
    cS
    wcel
    #
    wa
    #
    cT
    cU
    wpss
    #
    cT
    @6
    wpss
    #
    @6
    cU
    wpss
    #
    wa
    #
    vs
    cS
    wrex
    #
    wn
    #
    wa
    #
    wa
    #
    cT
    cU
    cC
    wbr
    @25
    wph
    @16
    @17
    @15
    @26
    wb
    lcvfbr.t
    lcvfbr.u
    @13
    @16
    @3
    wa
    #
    cT
    @2
    wpss
    #
    @20
    @8
    wa
    #
    vs
    cS
    wrex
    #
    wn
    #
    wa
    #
    wa
    @26
    vt
    vu
    cT
    cU
    cS
    cS
    @14
    @0
    cT
    wceq
    #
    @4
    @27
    @12
    @32
    @33
    @1
    @16
    @3
    @0
    cT
    cS
    eleq1
    anbi1d
    @33
    @5
    @28
    @11
    @31
    @0
    cT
    @2
    psseq1
    @33
    @10
    @30
    @33
    @9
    @29
    vs
    cS
    @33
    @7
    @20
    @8
    @0
    cT
    @6
    psseq1
    anbi1d
    rexbidv
    notbid
    anbi12d
    anbi12d
    @2
    cU
    wceq
    #
    @27
    @18
    @32
    @25
    @34
    @3
    @17
    @16
    @2
    cU
    cS
    eleq1
    anbi2d
    @34
    @28
    @19
    @31
    @24
    @2
    cU
    cT
    psseq2
    @34
    @30
    @23
    @34
    @29
    @22
    vs
    cS
    @34
    @8
    @21
    @20
    @2
    cU
    @6
    psseq2
    anbi2d
    rexbidv
    notbid
    anbi12d
    anbi12d
    @14
    eqid
    brabg
    syl2anc
    wph
    cC
    @14
    cT
    cU
    wph
    vu
    vt
    cC
    cS
    cW
    cX
    vs
    lcvfbr.s
    lcvfbr.c
    lcvfbr.w
    lcvfbr
    breqd
    wph
    @18
    @25
    wph
    @16
    @17
    lcvfbr.t
    lcvfbr.u
    jca
    biantrurd
    3bitr4d
end
