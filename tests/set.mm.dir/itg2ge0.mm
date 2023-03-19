include "cr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "csn.mm"
include "cxp.mm"
include "citg1.mm"
include "cfv.mm"
include "citg2.mm"
include "cle.mm"
include "itg10.mm"
include "cofr.mm"
include "wbr.mm"
include "cv.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "ffvelrn.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "0xr.mm"
include "pnfxr.mm"
include "elicc1.mm"
include "mp2an.mm"
include "simp2bi.mm"
include "syl.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "wfn.mm"
include "0re.mm"
include "fnconstg.mm"
include "mp1i.mm"
include "ffn.mm"
include "reex.mm"
include "a1i.mm"
include "inidm.mm"
include "wceq.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "adantl.mm"
include "eqidd.mm"
include "ofrfval.mm"
include "mpbird.mm"
include "cdm.mm"
include "i1f0.mm"
include "itg2ub.mm"
include "mp3an2.mm"
include "mpdan.mm"
include "syl5eqbrr.mm"

theorem itg2ge0
  let cF: class F
  let vg: setvar g
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vh: setvar h
  let vy: setvar y
  let cG: class G


  assert |- ( F : RR --> ( 0 [,] +oo ) -> 0 <_ ( S.2 ` F ) )

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
    cc0
    cr
    cc0
    csn
    cxp
    #
    citg1
    cfv
    #
    cF
    citg2
    cfv
    #
    cle
    itg10
    @1
    @2
    cF
    cle
    cofr
    wbr
    #
    @3
    @4
    cle
    wbr
    #
    @1
    @5
    cc0
    vy
    cv
    #
    cF
    cfv
    #
    cle
    wbr
    #
    vy
    cr
    wral
    @1
    @9
    vy
    cr
    @1
    @7
    cr
    wcel
    #
    wa
    #
    @8
    @0
    wcel
    #
    @9
    cr
    @0
    @7
    cF
    ffvelrn
    @12
    @8
    cxr
    wcel
    #
    @9
    @8
    cpnf
    cle
    wbr
    #
    cc0
    cxr
    wcel
    cpnf
    cxr
    wcel
    @12
    @13
    @9
    @14
    w3a
    wb
    0xr
    pnfxr
    cc0
    cpnf
    @8
    elicc1
    mp2an
    simp2bi
    syl
    ralrimiva
    @1
    vy
    cr
    cr
    cc0
    @8
    cle
    cr
    @2
    cF
    cvv
    cvv
    cc0
    cr
    wcel
    @2
    cr
    wfn
    @1
    0re
    cr
    cc0
    cr
    fnconstg
    mp1i
    cr
    @0
    cF
    ffn
    cr
    cvv
    wcel
    @1
    reex
    a1i
    #
    @15
    cr
    inidm
    @10
    @7
    @2
    cfv
    cc0
    wceq
    @1
    cr
    cc0
    @7
    c0ex
    fvconst2
    adantl
    @11
    @8
    eqidd
    ofrfval
    mpbird
    @1
    @2
    citg1
    cdm
    wcel
    @5
    @6
    i1f0
    cF
    @2
    itg2ub
    mp3an2
    mpdan
    syl5eqbrr
end
