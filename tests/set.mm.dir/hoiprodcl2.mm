include "cfv.mm"
include "cv.mm"
include "cico.mm"
include "ccom.mm"
include "cvol.mm"
include "cprod.mm"
include "cc0.mm"
include "cpnf.mm"
include "co.mm"
include "cr.mm"
include "cxp.mm"
include "cmap.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "coeq2.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "ralrimivw.mm"
include "prodeq2d.mm"
include "adantl.mm"
include "wcel.mm"
include "wf.mm"
include "cfn.mm"
include "wa.mm"
include "wb.mm"
include "reex.mm"
include "xpex.mm"
include "jca.mm"
include "elmapg.mm"
include "syl.mm"
include "mpbird.mm"
include "hoiprodcl.mm"
include "elexd.mm"
include "fvmptd.mm"
include "eqeltrd.mm"

theorem hoiprodcl2
  let wph: wff ph
  let vi: setvar i
  let vk: setvar k
  let cI: class I
  let cL: class L
  let cX: class X
  let vx: setvar x
  assume hoiprodcl2.kph: |- F/ k ph
  assume hoiprodcl2.x: |- ( ph -> X e. Fin )
  assume hoiprodcl2.l: |- L = ( i e. ( ( RR X. RR ) ^m X ) |-> prod_ k e. X ( vol ` ( ( [,) o. i ) ` k ) ) )
  assume hoiprodcl2.i: |- ( ph -> I : X --> ( RR X. RR ) )

  disjoint I i
  disjoint I k
  disjoint i k
  disjoint X i
  disjoint X k
  disjoint i ph
  disjoint k x
  assert |- ( ph -> ( L ` I ) e. ( 0 [,) +oo ) )

  proof
    wph
    cI
    cL
    cfv
    cX
    vk
    cv
    #
    cico
    cI
    ccom
    #
    cfv
    #
    cvol
    cfv
    #
    vk
    cprod
    #
    cc0
    cpnf
    cico
    co
    #
    wph
    vi
    cI
    cX
    @0
    cico
    vi
    cv
    #
    ccom
    #
    cfv
    #
    cvol
    cfv
    #
    vk
    cprod
    #
    @4
    cr
    cr
    cxp
    #
    cX
    cmap
    co
    #
    cL
    cvv
    cL
    vi
    @12
    @10
    cmpt
    wceq
    wph
    hoiprodcl2.l
    a1i
    @6
    cI
    wceq
    #
    @10
    @4
    wceq
    wph
    @13
    cX
    @9
    @3
    vk
    @13
    @9
    @3
    wceq
    vk
    cX
    @13
    @8
    @2
    cvol
    @13
    @0
    @7
    @1
    @6
    cI
    cico
    coeq2
    fveq1d
    fveq2d
    ralrimivw
    prodeq2d
    adantl
    wph
    cI
    @12
    wcel
    #
    cX
    @11
    cI
    wf
    #
    hoiprodcl2.i
    wph
    @11
    cvv
    wcel
    #
    cX
    cfn
    wcel
    #
    wa
    @14
    @15
    wb
    wph
    @16
    @17
    @16
    wph
    cr
    cr
    reex
    reex
    xpex
    a1i
    hoiprodcl2.x
    jca
    @11
    cX
    cI
    cvv
    cfn
    elmapg
    syl
    mpbird
    wph
    @4
    @5
    wph
    vk
    cI
    cX
    hoiprodcl2.kph
    hoiprodcl2.x
    hoiprodcl2.i
    hoiprodcl
    #
    elexd
    fvmptd
    @18
    eqeltrd
end
