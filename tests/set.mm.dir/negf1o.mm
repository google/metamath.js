include "cr.mm"
include "wss.mm"
include "cv.mm"
include "cneg.mm"
include "wcel.mm"
include "crab.mm"
include "wf1o.mm"
include "ccnv.mm"
include "cmpt.mm"
include "wceq.mm"
include "wa.mm"
include "ssel.mm"
include "renegcl.mm"
include "syl6.mm"
include "imp.mm"
include "wi.mm"
include "cc.mm"
include "recn.mm"
include "negneg.mm"
include "eqcomd.mm"
include "syl.mm"
include "eleq1d.mm"
include "biimpcd.mm"
include "adantl.mm"
include "mpd.mm"
include "negeq.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "weq.mm"
include "simpr.mm"
include "a1i.mm"
include "syl5bi.mm"
include "wb.mm"
include "syl6com.mm"
include "ad3antrrr.mm"
include "negcon2.mm"
include "syl2anc.mm"
include "exp31.mm"
include "sylbi.mm"
include "impcom.mm"
include "f1ocnv2d.mm"
include "simpld.mm"

theorem negf1o
  let vx: setvar x
  let cA: class A
  let vn: setvar n
  let cF: class F
  let vy: setvar y
  assume negf1o.1: |- F = ( x e. A |-> -u x )

  disjoint A n
  disjoint A x
  disjoint n x
  disjoint A y
  disjoint n y
  disjoint x y
  assert |- ( A C_ RR -> F : A -1-1-onto-> { n e. RR | -u n e. A } )

  proof
    cA
    cr
    wss
    #
    cA
    vn
    cv
    #
    cneg
    #
    cA
    wcel
    #
    vn
    cr
    crab
    #
    cF
    wf1o
    cF
    ccnv
    vy
    @4
    vy
    cv
    #
    cneg
    #
    cmpt
    wceq
    @0
    vx
    vy
    cA
    @4
    vx
    cv
    #
    cneg
    #
    @6
    cF
    negf1o.1
    @0
    @7
    cA
    wcel
    #
    wa
    #
    @8
    cr
    wcel
    #
    @8
    cneg
    #
    cA
    wcel
    #
    @8
    @4
    wcel
    @0
    @9
    @11
    @0
    @9
    @7
    cr
    wcel
    #
    @11
    cA
    cr
    @7
    ssel
    #
    @7
    renegcl
    syl6
    imp
    @10
    @14
    @13
    @0
    @9
    @14
    @15
    imp
    @9
    @14
    @13
    wi
    @0
    @14
    @9
    @13
    @14
    @7
    @12
    cA
    @14
    @7
    cc
    wcel
    #
    @7
    @12
    wceq
    @7
    recn
    #
    @16
    @12
    @7
    @7
    negneg
    eqcomd
    syl
    eleq1d
    biimpcd
    adantl
    mpd
    @3
    @13
    vn
    @8
    cr
    @1
    @8
    wceq
    @2
    @12
    cA
    @1
    @8
    negeq
    eleq1d
    elrab
    sylanbrc
    @0
    @5
    @4
    wcel
    #
    @6
    cA
    wcel
    #
    @18
    @5
    cr
    wcel
    #
    @19
    wa
    #
    @0
    @19
    @3
    @19
    vn
    @5
    cr
    vn
    vy
    weq
    @2
    @6
    cA
    @1
    @5
    negeq
    eleq1d
    elrab
    #
    @21
    @19
    wi
    @0
    @20
    @19
    simpr
    a1i
    syl5bi
    imp
    @9
    @18
    wa
    @0
    @7
    @6
    wceq
    @5
    @8
    wceq
    wb
    #
    @18
    @9
    @0
    @23
    wi
    #
    @18
    @21
    @9
    @24
    wi
    @22
    @21
    @9
    @0
    @23
    @21
    @9
    wa
    #
    @0
    wa
    @16
    @5
    cc
    wcel
    #
    @23
    @25
    @0
    @16
    @9
    @0
    @16
    wi
    @21
    @0
    @9
    @14
    @16
    @15
    @17
    syl6com
    adantl
    imp
    @20
    @26
    @19
    @9
    @0
    @5
    recn
    ad3antrrr
    @7
    @5
    negcon2
    syl2anc
    exp31
    sylbi
    impcom
    impcom
    f1ocnv2d
    simpld
end
