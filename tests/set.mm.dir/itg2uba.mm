include "citg1.mm"
include "cfv.mm"
include "cr.mm"
include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "cdm.mm"
include "itg1cl.mm"
include "syl.mm"
include "rexrd.mm"
include "cdif.mm"
include "cvol.mm"
include "wss.mm"
include "covol.mm"
include "wceq.mm"
include "nulmbl.mm"
include "syl2anc.mm"
include "cmmbl.mm"
include "wn.mm"
include "ifnot.mm"
include "eldif.mm"
include "baibr.mm"
include "ifbid.mm"
include "syl5eqr.mm"
include "mpteq2ia.mm"
include "i1fres.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cxr.mm"
include "itg2cl.mm"
include "wa.mm"
include "cle.mm"
include "i1ff.mm"
include "eldifi.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "leidd.mm"
include "eleq1.mm"
include "fveq2.mm"
include "ifbieq2d.mm"
include "eqid.mm"
include "c0ex.mm"
include "fvex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "iffalse.mm"
include "sylan9eq.mm"
include "sylbi.mm"
include "adantl.mm"
include "breqtrrd.mm"
include "itg1lea.mm"
include "cofr.mm"
include "wbr.mm"
include "wral.mm"
include "iftrue.mm"
include "ffvelrnda.mm"
include "elxrge0.mm"
include "sylib.mm"
include "simprd.mm"
include "adantr.mm"
include "eqbrtrd.mm"
include "sylan2br.mm"
include "anassrs.mm"
include "pm2.61dan.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "reex.mm"
include "a1i.mm"
include "fvexd.mm"
include "eqidd.mm"
include "feqmptd.mm"
include "ofrfval2.mm"
include "mpbird.mm"
include "itg2ub.mm"
include "syl3anc.mm"
include "xrletrd.mm"

theorem itg2uba
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cG: class G
  let vy: setvar y
  assume itg2uba.1: |- ( ph -> F : RR --> ( 0 [,] +oo ) )
  assume itg2uba.2: |- ( ph -> G e. dom S.1 )
  assume itg2uba.3: |- ( ph -> A C_ RR )
  assume itg2uba.4: |- ( ph -> ( vol* ` A ) = 0 )
  assume itg2uba.5: |- ( ( ph /\ x e. ( RR \ A ) ) -> ( G ` x ) <_ ( F ` x ) )

  disjoint A x
  disjoint F x
  disjoint G x
  disjoint ph x
  disjoint x y
  disjoint A y
  disjoint G y
  disjoint ph y
  assert |- ( ph -> ( S.1 ` G ) <_ ( S.2 ` F ) )

  proof
    wph
    cG
    citg1
    cfv
    #
    vx
    cr
    vx
    cv
    #
    cA
    wcel
    #
    cc0
    @1
    cG
    cfv
    #
    cif
    #
    cmpt
    #
    citg1
    cfv
    #
    cF
    citg2
    cfv
    #
    wph
    @0
    wph
    cG
    citg1
    cdm
    #
    wcel
    #
    @0
    cr
    wcel
    itg2uba.2
    cG
    itg1cl
    syl
    rexrd
    wph
    @6
    wph
    @5
    @8
    wcel
    #
    @6
    cr
    wcel
    wph
    @9
    cr
    cA
    cdif
    #
    cvol
    cdm
    #
    wcel
    #
    @10
    itg2uba.2
    wph
    cA
    @12
    wcel
    #
    @13
    wph
    cA
    cr
    wss
    cA
    covol
    cfv
    cc0
    wceq
    @14
    itg2uba.3
    itg2uba.4
    cA
    nulmbl
    syl2anc
    cA
    cmmbl
    syl
    vx
    @11
    cG
    @5
    vx
    cr
    @4
    @1
    @11
    wcel
    #
    @3
    cc0
    cif
    #
    @1
    cr
    wcel
    #
    @4
    @2
    wn
    #
    @3
    cc0
    cif
    @16
    @2
    @3
    cc0
    ifnot
    @17
    @18
    @15
    @3
    cc0
    @15
    @17
    @18
    @1
    cr
    cA
    eldif
    #
    baibr
    ifbid
    syl5eqr
    mpteq2ia
    i1fres
    syl2anc
    #
    @5
    itg1cl
    syl
    rexrd
    wph
    cr
    cc0
    cpnf
    cicc
    co
    #
    cF
    wf
    #
    @7
    cxr
    wcel
    itg2uba.1
    cF
    itg2cl
    syl
    wph
    vy
    cA
    cG
    @5
    itg2uba.2
    itg2uba.3
    itg2uba.4
    @20
    wph
    vy
    cv
    #
    @11
    wcel
    #
    wa
    #
    @23
    cG
    cfv
    #
    @26
    @23
    @5
    cfv
    #
    cle
    @25
    @26
    wph
    cr
    cr
    cG
    wf
    #
    @23
    cr
    wcel
    #
    @26
    cr
    wcel
    @24
    wph
    @9
    @28
    itg2uba.2
    cG
    i1ff
    syl
    @23
    cr
    cA
    eldifi
    cr
    cr
    @23
    cG
    ffvelrn
    syl2an
    leidd
    @24
    @27
    @26
    wceq
    #
    wph
    @24
    @29
    @23
    cA
    wcel
    #
    wn
    #
    wa
    @30
    @23
    cr
    cA
    eldif
    @29
    @32
    @27
    @31
    cc0
    @26
    cif
    #
    @26
    vx
    @23
    @4
    @33
    cr
    @5
    @1
    @23
    wceq
    @2
    @31
    @3
    @26
    cc0
    @1
    @23
    cA
    eleq1
    @1
    @23
    cG
    fveq2
    ifbieq2d
    @5
    eqid
    @31
    cc0
    @26
    c0ex
    @23
    cG
    fvex
    ifex
    fvmpt
    @31
    cc0
    @26
    iffalse
    sylan9eq
    sylbi
    adantl
    breqtrrd
    itg1lea
    wph
    @22
    @10
    @5
    cF
    cle
    cofr
    wbr
    #
    @6
    @7
    cle
    wbr
    itg2uba.1
    @20
    wph
    @34
    @4
    @1
    cF
    cfv
    #
    cle
    wbr
    #
    vx
    cr
    wral
    wph
    @36
    vx
    cr
    wph
    @17
    wa
    #
    @2
    @36
    @37
    @2
    wa
    @4
    cc0
    @35
    cle
    @2
    @4
    cc0
    wceq
    @37
    @2
    cc0
    @3
    iftrue
    adantl
    @37
    cc0
    @35
    cle
    wbr
    #
    @2
    @37
    @35
    cxr
    wcel
    #
    @38
    @37
    @35
    @21
    wcel
    @39
    @38
    wa
    wph
    cr
    @21
    @1
    cF
    itg2uba.1
    ffvelrnda
    @35
    elxrge0
    sylib
    simprd
    adantr
    eqbrtrd
    @37
    @18
    wa
    @4
    @3
    @35
    cle
    @18
    @4
    @3
    wceq
    @37
    @2
    cc0
    @3
    iffalse
    adantl
    wph
    @17
    @18
    @3
    @35
    cle
    wbr
    #
    @17
    @18
    wa
    wph
    @15
    @40
    @19
    itg2uba.5
    sylan2br
    anassrs
    eqbrtrd
    pm2.61dan
    ralrimiva
    wph
    vx
    cr
    @4
    @35
    cle
    @5
    cF
    cvv
    cvv
    cvv
    cr
    cvv
    wcel
    wph
    reex
    a1i
    @4
    cvv
    wcel
    @37
    @2
    cc0
    @3
    c0ex
    @1
    cG
    fvex
    ifex
    a1i
    @37
    @1
    cF
    fvexd
    wph
    @5
    eqidd
    wph
    vx
    cr
    @21
    cF
    itg2uba.1
    feqmptd
    ofrfval2
    mpbird
    cF
    @5
    itg2ub
    syl3anc
    xrletrd
end
