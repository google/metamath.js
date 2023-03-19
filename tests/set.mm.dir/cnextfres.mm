include "ccnext.mm"
include "co.mm"
include "cfv.mm"
include "wfun.mm"
include "wbr.mm"
include "wceq.mm"
include "ctop.mm"
include "wcel.mm"
include "cha.mm"
include "wf.mm"
include "wss.mm"
include "crest.mm"
include "cuni.mm"
include "ccn.mm"
include "eqid.mm"
include "cnf.mm"
include "syl.mm"
include "restuni.mm"
include "syl2anc.mm"
include "feq2d.mm"
include "mpbird.mm"
include "cnextfun.mm"
include "syl22anc.mm"
include "cop.mm"
include "ccl.mm"
include "cv.mm"
include "csn.mm"
include "cnei.mm"
include "cflf.mm"
include "cxp.mm"
include "ciun.mm"
include "wa.mm"
include "sscls.mm"
include "sseldd.mm"
include "flfcntr.mm"
include "jca.mm"
include "sneq.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "fveq1d.mm"
include "opeliunxp2.mm"
include "sylibr.mm"
include "haustop.mm"
include "cnextfval.mm"
include "eleq2d.mm"
include "df-br.mm"
include "funbrfv.mm"
include "imp.mm"

theorem cnextfres
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let vx: setvar x
  assume cnextfres.c: |- C = U. J
  assume cnextfres.b: |- B = U. K
  assume cnextfres.j: |- ( ph -> J e. Top )
  assume cnextfres.k: |- ( ph -> K e. Haus )
  assume cnextfres.a: |- ( ph -> A C_ C )
  assume cnextfres.1: |- ( ph -> F e. ( ( J |`t A ) Cn K ) )
  assume cnextfres.x: |- ( ph -> X e. A )


  assert |- ( ph -> ( ( ( J CnExt K ) ` F ) ` X ) = ( F ` X ) )

  proof
    wph
    cF
    cJ
    cK
    ccnext
    co
    cfv
    #
    wfun
    #
    cX
    cX
    cF
    cfv
    #
    @0
    wbr
    #
    cX
    @0
    cfv
    @2
    wceq
    #
    wph
    cJ
    ctop
    wcel
    #
    cK
    cha
    wcel
    #
    cA
    cB
    cF
    wf
    #
    cA
    cC
    wss
    #
    @1
    cnextfres.j
    cnextfres.k
    wph
    @7
    cJ
    cA
    crest
    co
    #
    cuni
    #
    cB
    cF
    wf
    #
    wph
    cF
    @9
    cK
    ccn
    co
    wcel
    @11
    cnextfres.1
    cF
    @9
    cK
    @10
    cB
    @10
    eqid
    cnextfres.b
    cnf
    syl
    wph
    cA
    @10
    cB
    cF
    wph
    @5
    @8
    cA
    @10
    wceq
    cnextfres.j
    cnextfres.a
    cA
    cJ
    cC
    cnextfres.c
    restuni
    syl2anc
    feq2d
    mpbird
    #
    cnextfres.a
    cA
    cB
    cC
    cF
    cJ
    cK
    cnextfres.c
    cnextfres.b
    cnextfun
    syl22anc
    wph
    cX
    @2
    cop
    #
    @0
    wcel
    #
    @3
    wph
    @14
    @13
    vx
    cA
    cJ
    ccl
    cfv
    cfv
    #
    vx
    cv
    #
    csn
    #
    cF
    cK
    @17
    cJ
    cnei
    cfv
    #
    cfv
    #
    cA
    crest
    co
    #
    cflf
    co
    #
    cfv
    #
    cxp
    ciun
    #
    wcel
    #
    wph
    cX
    @15
    wcel
    #
    @2
    cF
    cK
    cX
    csn
    #
    @18
    cfv
    #
    cA
    crest
    co
    #
    cflf
    co
    #
    cfv
    #
    wcel
    #
    wa
    @24
    wph
    @25
    @31
    wph
    cA
    @15
    cX
    wph
    @5
    @8
    cA
    @15
    wss
    cnextfres.j
    cnextfres.a
    cA
    cJ
    cC
    cnextfres.c
    sscls
    syl2anc
    cnextfres.x
    sseldd
    wph
    cA
    cB
    cC
    cF
    cJ
    cK
    cX
    cnextfres.c
    cnextfres.b
    cnextfres.j
    cnextfres.a
    cnextfres.1
    cnextfres.x
    flfcntr
    jca
    vx
    @15
    @22
    cX
    @2
    @30
    @16
    cX
    wceq
    #
    cF
    @21
    @29
    @32
    @20
    @28
    cK
    cflf
    @32
    @19
    @27
    cA
    crest
    @32
    @17
    @26
    @18
    @16
    cX
    sneq
    fveq2d
    oveq1d
    oveq2d
    fveq1d
    opeliunxp2
    sylibr
    wph
    @0
    @23
    @13
    wph
    @5
    cK
    ctop
    wcel
    #
    @7
    @8
    @0
    @23
    wceq
    cnextfres.j
    wph
    @6
    @33
    cnextfres.k
    cK
    haustop
    syl
    @12
    cnextfres.a
    vx
    cA
    cB
    cF
    cJ
    cK
    cC
    cnextfres.c
    cnextfres.b
    cnextfval
    syl22anc
    eleq2d
    mpbird
    cX
    @2
    @0
    df-br
    sylibr
    @1
    @3
    @4
    cX
    @2
    @0
    funbrfv
    imp
    syl2anc
end
