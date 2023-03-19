include "citg2.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cofr.mm"
include "citg1.mm"
include "wi.mm"
include "cdm.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "adantr.mm"
include "simprl.mm"
include "wss.mm"
include "covol.mm"
include "wceq.mm"
include "cdif.mm"
include "i1ff.mm"
include "ad2antrl.mm"
include "eldifi.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "rexrd.mm"
include "cxr.mm"
include "iccssxr.mm"
include "sseldi.mm"
include "simprr.mm"
include "cvv.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "reex.mm"
include "a1i.mm"
include "inidm.mm"
include "eqidd.mm"
include "ofrfval.mm"
include "mpbid.mm"
include "r19.21bi.mm"
include "sylan2.mm"
include "adantlr.mm"
include "xrletrd.mm"
include "itg2uba.mm"
include "expr.mm"
include "ralrimiva.mm"
include "wb.mm"
include "itg2cl.mm"
include "itg2leub.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem itg2lea
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cG: class G
  let vf: setvar f
  assume itg2lea.1: |- ( ph -> F : RR --> ( 0 [,] +oo ) )
  assume itg2lea.2: |- ( ph -> G : RR --> ( 0 [,] +oo ) )
  assume itg2lea.3: |- ( ph -> A C_ RR )
  assume itg2lea.4: |- ( ph -> ( vol* ` A ) = 0 )
  assume itg2lea.5: |- ( ( ph /\ x e. ( RR \ A ) ) -> ( F ` x ) <_ ( G ` x ) )

  disjoint A x
  disjoint F x
  disjoint G x
  disjoint ph x
  disjoint f x
  disjoint F f
  disjoint G f
  disjoint f ph
  assert |- ( ph -> ( S.2 ` F ) <_ ( S.2 ` G ) )

  proof
    wph
    cF
    citg2
    cfv
    cG
    citg2
    cfv
    #
    cle
    wbr
    #
    vf
    cv
    #
    cF
    cle
    cofr
    wbr
    #
    @2
    citg1
    cfv
    @0
    cle
    wbr
    #
    wi
    #
    vf
    citg1
    cdm
    #
    wral
    #
    wph
    @5
    vf
    @6
    wph
    @2
    @6
    wcel
    #
    @3
    @4
    wph
    @8
    @3
    wa
    #
    wa
    #
    vx
    cA
    cG
    @2
    wph
    cr
    cc0
    cpnf
    cicc
    co
    #
    cG
    wf
    #
    @9
    itg2lea.2
    adantr
    #
    wph
    @8
    @3
    simprl
    wph
    cA
    cr
    wss
    @9
    itg2lea.3
    adantr
    wph
    cA
    covol
    cfv
    cc0
    wceq
    @9
    itg2lea.4
    adantr
    @10
    vx
    cv
    #
    cr
    cA
    cdif
    wcel
    #
    wa
    #
    @14
    @2
    cfv
    #
    @14
    cF
    cfv
    #
    @14
    cG
    cfv
    #
    @16
    @17
    @10
    cr
    cr
    @2
    wf
    #
    @14
    cr
    wcel
    #
    @17
    cr
    wcel
    @15
    @8
    @20
    wph
    @3
    @2
    i1ff
    ad2antrl
    #
    @14
    cr
    cA
    eldifi
    #
    cr
    cr
    @14
    @2
    ffvelrn
    syl2an
    rexrd
    @16
    @11
    cxr
    @18
    cc0
    cpnf
    iccssxr
    #
    @10
    cr
    @11
    cF
    wf
    #
    @21
    @18
    @11
    wcel
    @15
    wph
    @25
    @9
    itg2lea.1
    adantr
    #
    @23
    cr
    @11
    @14
    cF
    ffvelrn
    syl2an
    sseldi
    @16
    @11
    cxr
    @19
    @24
    @10
    @12
    @21
    @19
    @11
    wcel
    @15
    @13
    @23
    cr
    @11
    @14
    cG
    ffvelrn
    syl2an
    sseldi
    @15
    @10
    @21
    @17
    @18
    cle
    wbr
    #
    @23
    @10
    @27
    vx
    cr
    @10
    @3
    @27
    vx
    cr
    wral
    wph
    @8
    @3
    simprr
    @10
    vx
    cr
    cr
    @17
    @18
    cle
    cr
    @2
    cF
    cvv
    cvv
    @10
    @20
    @2
    cr
    wfn
    @22
    cr
    cr
    @2
    ffn
    syl
    @10
    @25
    cF
    cr
    wfn
    @26
    cr
    @11
    cF
    ffn
    syl
    cr
    cvv
    wcel
    @10
    reex
    a1i
    #
    @28
    cr
    inidm
    @10
    @21
    wa
    #
    @17
    eqidd
    @29
    @18
    eqidd
    ofrfval
    mpbid
    r19.21bi
    sylan2
    wph
    @15
    @18
    @19
    cle
    wbr
    @9
    itg2lea.5
    adantlr
    xrletrd
    itg2uba
    expr
    ralrimiva
    wph
    @25
    @0
    cxr
    wcel
    #
    @1
    @7
    wb
    itg2lea.1
    wph
    @12
    @30
    itg2lea.2
    cG
    itg2cl
    syl
    @0
    vf
    cF
    itg2leub
    syl2anc
    mpbird
end
