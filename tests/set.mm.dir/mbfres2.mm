include "cmbf.mm"
include "wcel.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cvol.mm"
include "cdm.mm"
include "cioo.mm"
include "crn.mm"
include "wral.mm"
include "wa.mm"
include "cres.mm"
include "cun.mm"
include "wceq.mm"
include "reseq2d.mm"
include "cr.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "fnresdm.mm"
include "3syl.mm"
include "eqtr2d.mm"
include "adantr.mm"
include "resundi.mm"
include "syl6eq.mm"
include "cnveqd.mm"
include "cnvun.mm"
include "imaeq1d.mm"
include "imaundir.mm"
include "wb.mm"
include "ssun1.mm"
include "syl5sseq.mm"
include "fssresd.mm"
include "ismbf.mm"
include "syl.mm"
include "mpbid.mm"
include "r19.21bi.mm"
include "ssun2.mm"
include "unmbl.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "mpbird.mm"

theorem mbfres2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vx: setvar x
  assume mbfres2.1: |- ( ph -> F : A --> RR )
  assume mbfres2.2: |- ( ph -> ( F |` B ) e. MblFn )
  assume mbfres2.3: |- ( ph -> ( F |` C ) e. MblFn )
  assume mbfres2.4: |- ( ph -> ( B u. C ) = A )


  assert |- ( ph -> F e. MblFn )

  proof
    wph
    cF
    cmbf
    wcel
    #
    cF
    ccnv
    #
    vx
    cv
    #
    cima
    #
    cvol
    cdm
    #
    wcel
    #
    vx
    cioo
    crn
    #
    wral
    #
    wph
    @5
    vx
    @6
    wph
    @2
    @6
    wcel
    #
    wa
    #
    @3
    cF
    cB
    cres
    #
    ccnv
    #
    @2
    cima
    #
    cF
    cC
    cres
    #
    ccnv
    #
    @2
    cima
    #
    cun
    #
    @4
    @9
    @3
    @11
    @14
    cun
    #
    @2
    cima
    @16
    @9
    @1
    @17
    @2
    @9
    @1
    @10
    @13
    cun
    #
    ccnv
    @17
    @9
    cF
    @18
    @9
    cF
    cF
    cB
    cC
    cun
    #
    cres
    #
    @18
    wph
    cF
    @20
    wceq
    @8
    wph
    @20
    cF
    cA
    cres
    #
    cF
    wph
    @19
    cA
    cF
    mbfres2.4
    reseq2d
    wph
    cA
    cr
    cF
    wf
    #
    cF
    cA
    wfn
    @21
    cF
    wceq
    mbfres2.1
    cA
    cr
    cF
    ffn
    cA
    cF
    fnresdm
    3syl
    eqtr2d
    adantr
    cF
    cB
    cC
    resundi
    syl6eq
    cnveqd
    @10
    @13
    cnvun
    syl6eq
    imaeq1d
    @11
    @14
    @2
    imaundir
    syl6eq
    @9
    @12
    @4
    wcel
    #
    @15
    @4
    wcel
    #
    @16
    @4
    wcel
    wph
    @23
    vx
    @6
    wph
    @10
    cmbf
    wcel
    #
    @23
    vx
    @6
    wral
    #
    mbfres2.2
    wph
    cB
    cr
    @10
    wf
    @25
    @26
    wb
    wph
    cA
    cr
    cB
    cF
    mbfres2.1
    wph
    @19
    cB
    cA
    cB
    cC
    ssun1
    mbfres2.4
    syl5sseq
    fssresd
    vx
    cB
    @10
    ismbf
    syl
    mpbid
    r19.21bi
    wph
    @24
    vx
    @6
    wph
    @13
    cmbf
    wcel
    #
    @24
    vx
    @6
    wral
    #
    mbfres2.3
    wph
    cC
    cr
    @13
    wf
    @27
    @28
    wb
    wph
    cA
    cr
    cC
    cF
    mbfres2.1
    wph
    @19
    cC
    cA
    cC
    cB
    ssun2
    mbfres2.4
    syl5sseq
    fssresd
    vx
    cC
    @13
    ismbf
    syl
    mpbid
    r19.21bi
    @12
    @15
    unmbl
    syl2anc
    eqeltrd
    ralrimiva
    wph
    @22
    @0
    @7
    wb
    mbfres2.1
    vx
    cA
    cF
    ismbf
    syl
    mpbird
end
