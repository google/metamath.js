include "cr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "w3a.mm"
include "citg2.mm"
include "cfv.mm"
include "cv.mm"
include "citg1.mm"
include "wi.mm"
include "cdm.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cxr.mm"
include "cvv.mm"
include "reex.mm"
include "a1i.mm"
include "wss.mm"
include "i1ff.mm"
include "adantl.mm"
include "ressxr.mm"
include "fss.mm"
include "sylancl.mm"
include "simpll.mm"
include "iccssxr.mm"
include "simplr.mm"
include "xrletr.mm"
include "caoftrn.mm"
include "simprl.mm"
include "simprr.mm"
include "itg2ub.mm"
include "syl3anc.mm"
include "expr.mm"
include "syld.mm"
include "ancomsd.mm"
include "exp4b.mm"
include "com23.mm"
include "3impia.mm"
include "ralrimiv.mm"
include "wb.mm"
include "simp1.mm"
include "itg2cl.mm"
include "3ad2ant2.mm"
include "itg2leub.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem itg2le
  let cF: class F
  let cG: class G
  let vg: setvar g
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vh: setvar h
  let vy: setvar y


  assert |- ( ( F : RR --> ( 0 [,] +oo ) /\ G : RR --> ( 0 [,] +oo ) /\ F oR <_ G ) -> ( S.2 ` F ) <_ ( S.2 ` G ) )

  proof
    cr
    cc0
    cpnf
    cicc
    co
    #
    cF
    wf
    #
    cr
    @0
    cG
    wf
    #
    cF
    cG
    cle
    cofr
    #
    wbr
    #
    w3a
    #
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
    vh
    cv
    #
    cF
    @3
    wbr
    #
    @8
    citg1
    cfv
    @6
    cle
    wbr
    #
    wi
    #
    vh
    citg1
    cdm
    #
    wral
    #
    @5
    @11
    vh
    @12
    @1
    @2
    @4
    @8
    @12
    wcel
    #
    @11
    wi
    @1
    @2
    wa
    #
    @14
    @4
    @11
    @15
    @14
    @4
    @9
    @10
    @15
    @14
    wa
    #
    @9
    @4
    @10
    @16
    @9
    @4
    wa
    @8
    cG
    @3
    wbr
    #
    @10
    @16
    vx
    vy
    vz
    cr
    cle
    cxr
    cle
    cle
    @8
    cF
    cG
    cvv
    cr
    cvv
    wcel
    @16
    reex
    a1i
    @16
    cr
    cr
    @8
    wf
    #
    cr
    cxr
    wss
    cr
    cxr
    @8
    wf
    @14
    @18
    @15
    @8
    i1ff
    adantl
    ressxr
    cr
    cr
    cxr
    @8
    fss
    sylancl
    @16
    @1
    @0
    cxr
    wss
    #
    cr
    cxr
    cF
    wf
    @1
    @2
    @14
    simpll
    cc0
    cpnf
    iccssxr
    #
    cr
    @0
    cxr
    cF
    fss
    sylancl
    @16
    @2
    @19
    cr
    cxr
    cG
    wf
    @1
    @2
    @14
    simplr
    @20
    cr
    @0
    cxr
    cG
    fss
    sylancl
    vx
    cv
    #
    cxr
    wcel
    vy
    cv
    #
    cxr
    wcel
    vz
    cv
    #
    cxr
    wcel
    w3a
    @21
    @22
    cle
    wbr
    @22
    @23
    cle
    wbr
    wa
    @21
    @23
    cle
    wbr
    wi
    @16
    @21
    @22
    @23
    xrletr
    adantl
    caoftrn
    @15
    @14
    @17
    @10
    @15
    @14
    @17
    wa
    #
    wa
    @2
    @14
    @17
    @10
    @1
    @2
    @24
    simplr
    @15
    @14
    @17
    simprl
    @15
    @14
    @17
    simprr
    cG
    @8
    itg2ub
    syl3anc
    expr
    syld
    ancomsd
    exp4b
    com23
    3impia
    ralrimiv
    @5
    @1
    @6
    cxr
    wcel
    #
    @7
    @13
    wb
    @1
    @2
    @4
    simp1
    @2
    @1
    @25
    @4
    cG
    itg2cl
    3ad2ant2
    @6
    vh
    cF
    itg2leub
    syl2anc
    mpbird
end
