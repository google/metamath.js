include "cr.mm"
include "clt.mm"
include "ccnv.mm"
include "wiso.mm"
include "wceq.mm"
include "wf1o.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "cneg.mm"
include "cmpt.mm"
include "wa.mm"
include "wtru.mm"
include "wcel.mm"
include "simpr.mm"
include "renegcld.mm"
include "cc.mm"
include "recn.mm"
include "negcon2.mm"
include "syl2an.mm"
include "adantl.mm"
include "f1ocnv2d.mm"
include "trud.mm"
include "simpli.mm"
include "ltneg.mm"
include "negex.mm"
include "brcnv.mm"
include "syl6bbr.mm"
include "negeq.mm"
include "fvmpt.mm"
include "breqan12d.mm"
include "bitr4d.mm"
include "rgen2a.mm"
include "df-isom.mm"
include "mpbir2an.mm"
include "cbvmptv.mm"
include "simpri.mm"
include "3eqtr4i.mm"
include "pm3.2i.mm"

theorem negiso
  let vx: setvar x
  let cF: class F
  let vy: setvar y
  let vz: setvar z
  assume negiso.1: |- F = ( x e. RR |-> -u x )


  assert |- ( F Isom < , `' < ( RR , RR ) /\ `' F = F )

  proof
    cr
    cr
    clt
    clt
    ccnv
    #
    cF
    wiso
    #
    cF
    ccnv
    #
    cF
    wceq
    @1
    cr
    cr
    cF
    wf1o
    #
    vz
    cv
    #
    vy
    cv
    #
    clt
    wbr
    #
    @4
    cF
    cfv
    #
    @5
    cF
    cfv
    #
    @0
    wbr
    #
    wb
    #
    vy
    cr
    wral
    vz
    cr
    wral
    @3
    @2
    vy
    cr
    @5
    cneg
    #
    cmpt
    #
    wceq
    #
    @3
    @13
    wa
    wtru
    vx
    vy
    cr
    cr
    vx
    cv
    #
    cneg
    #
    @11
    cF
    negiso.1
    wtru
    @14
    cr
    wcel
    #
    wa
    @14
    wtru
    @16
    simpr
    renegcld
    wtru
    @5
    cr
    wcel
    #
    wa
    @5
    wtru
    @17
    simpr
    renegcld
    @16
    @17
    wa
    @14
    @11
    wceq
    @5
    @15
    wceq
    wb
    #
    wtru
    @16
    @14
    cc
    wcel
    @5
    cc
    wcel
    @18
    @17
    @14
    recn
    @5
    recn
    @14
    @5
    negcon2
    syl2an
    adantl
    f1ocnv2d
    trud
    #
    simpli
    @10
    vz
    vy
    cr
    @4
    cr
    wcel
    #
    @17
    wa
    #
    @6
    @4
    cneg
    #
    @11
    @0
    wbr
    #
    @9
    @21
    @6
    @11
    @22
    clt
    wbr
    @23
    @4
    @5
    ltneg
    @22
    @11
    clt
    @4
    negex
    #
    @5
    negex
    #
    brcnv
    syl6bbr
    @20
    @17
    @7
    @22
    @8
    @11
    @0
    vx
    @4
    @15
    @22
    cr
    cF
    @14
    @4
    negeq
    negiso.1
    @24
    fvmpt
    vx
    @5
    @15
    @11
    cr
    cF
    @14
    @5
    negeq
    negiso.1
    @25
    fvmpt
    breqan12d
    bitr4d
    rgen2a
    vz
    vy
    cr
    cr
    clt
    @0
    cF
    df-isom
    mpbir2an
    @12
    vx
    cr
    @15
    cmpt
    @2
    cF
    vy
    vx
    cr
    @11
    @15
    @5
    @14
    negeq
    cbvmptv
    @3
    @13
    @19
    simpri
    negiso.1
    3eqtr4i
    pm3.2i
end
