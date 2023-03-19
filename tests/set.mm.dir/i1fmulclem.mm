include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cr.mm"
include "wcel.mm"
include "csn.mm"
include "cxp.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "ccnv.mm"
include "cima.mm"
include "cdiv.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cvv.mm"
include "reex.mm"
include "a1i.mm"
include "wf.mm"
include "wfn.mm"
include "citg1.mm"
include "cdm.mm"
include "i1ff.mm"
include "syl.mm"
include "ffn.mm"
include "eqidd.mm"
include "ofc1.mm"
include "adantlr.mm"
include "eqeq1d.mm"
include "eqcom.mm"
include "simplr.mm"
include "recnd.mm"
include "ad3antrrr.mm"
include "ad2antrr.mm"
include "ffvelrnda.mm"
include "simpllr.mm"
include "divmuld.mm"
include "syl5bb.mm"
include "bitr4d.mm"
include "pm5.32da.mm"
include "wb.mm"
include "remulcl.mm"
include "adantl.mm"
include "fconstg.mm"
include "snssd.mm"
include "fssd.mm"
include "inidm.mm"
include "off.mm"
include "fniniseg.mm"
include "3bitr4d.mm"
include "eqrdv.mm"

theorem i1fmulclem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume i1fmulc.2: |- ( ph -> F e. dom S.1 )
  assume i1fmulc.3: |- ( ph -> A e. RR )


  assert |- ( ( ( ph /\ A =/= 0 ) /\ B e. RR ) -> ( `' ( ( RR X. { A } ) oF x. F ) " { B } ) = ( `' F " { ( B / A ) } ) )

  proof
    wph
    cA
    cc0
    wne
    #
    wa
    #
    cB
    cr
    wcel
    #
    wa
    #
    vz
    cr
    cA
    csn
    #
    cxp
    #
    cF
    cmul
    cof
    co
    #
    ccnv
    cB
    csn
    cima
    #
    cF
    ccnv
    cB
    cA
    cdiv
    co
    #
    csn
    cima
    #
    @3
    vz
    cv
    #
    cr
    wcel
    #
    @10
    @6
    cfv
    #
    cB
    wceq
    #
    wa
    #
    @11
    @10
    cF
    cfv
    #
    @8
    wceq
    #
    wa
    #
    @10
    @7
    wcel
    #
    @10
    @9
    wcel
    #
    @3
    @11
    @13
    @16
    @3
    @11
    wa
    #
    @13
    cA
    @15
    cmul
    co
    #
    cB
    wceq
    #
    @16
    @20
    @12
    @21
    cB
    @1
    @11
    @12
    @21
    wceq
    #
    @2
    wph
    @11
    @23
    @0
    wph
    cr
    cA
    @15
    cmul
    cF
    cvv
    cr
    @10
    cr
    cvv
    wcel
    wph
    reex
    a1i
    #
    i1fmulc.3
    wph
    cr
    cr
    cF
    wf
    #
    cF
    cr
    wfn
    #
    wph
    cF
    citg1
    cdm
    wcel
    @25
    i1fmulc.2
    cF
    i1ff
    syl
    #
    cr
    cr
    cF
    ffn
    #
    syl
    wph
    @11
    wa
    @15
    eqidd
    ofc1
    adantlr
    adantlr
    eqeq1d
    @16
    @8
    @15
    wceq
    @20
    @22
    @15
    @8
    eqcom
    @20
    cB
    cA
    @15
    @20
    cB
    @1
    @2
    @11
    simplr
    recnd
    @20
    cA
    wph
    cA
    cr
    wcel
    #
    @0
    @2
    @11
    i1fmulc.3
    ad3antrrr
    recnd
    @20
    @15
    @3
    cr
    cr
    @10
    cF
    wph
    @25
    @0
    @2
    @27
    ad2antrr
    #
    ffvelrnda
    recnd
    wph
    @0
    @2
    @11
    simpllr
    divmuld
    syl5bb
    bitr4d
    pm5.32da
    @3
    @6
    cr
    wfn
    #
    @18
    @14
    wb
    @3
    cr
    cr
    @6
    wf
    #
    @31
    wph
    @32
    @0
    @2
    wph
    vx
    vy
    cr
    cr
    cr
    cmul
    cr
    cr
    cr
    @5
    cF
    cvv
    cvv
    vx
    cv
    #
    cr
    wcel
    vy
    cv
    #
    cr
    wcel
    wa
    @33
    @34
    cmul
    co
    cr
    wcel
    wph
    @33
    @34
    remulcl
    adantl
    wph
    cr
    @4
    cr
    @5
    wph
    @29
    cr
    @4
    @5
    wf
    i1fmulc.3
    cr
    cA
    cr
    fconstg
    syl
    wph
    cA
    cr
    i1fmulc.3
    snssd
    fssd
    @27
    @24
    @24
    cr
    inidm
    off
    ad2antrr
    cr
    cr
    @6
    ffn
    syl
    cr
    cB
    @10
    @6
    fniniseg
    syl
    @3
    @26
    @19
    @17
    wb
    @3
    @25
    @26
    @30
    @28
    syl
    cr
    @8
    @10
    cF
    fniniseg
    syl
    3bitr4d
    eqrdv
end
