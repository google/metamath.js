include "chil.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "csh.mm"
include "wcel.mm"
include "cn.mm"
include "cv.mm"
include "wf.mm"
include "chli.mm"
include "wbr.mm"
include "wrex.mm"
include "wi.mm"
include "ccau.mm"
include "wral.mm"
include "cch.mm"
include "ocsh.mm"
include "wa.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cdm.mm"
include "ax-hcompl.mm"
include "vex.mm"
include "breldm.mm"
include "rexlimivw.mm"
include "syl.mm"
include "ad2antlr.mm"
include "hlimf.mm"
include "ffvelrni.mm"
include "simplll.mm"
include "simpllr.mm"
include "simplr.mm"
include "simpr.mm"
include "occllem.mm"
include "ralrimiva.mm"
include "wb.mm"
include "ocel.mm"
include "ad2antrr.mm"
include "mpbir2and.mm"
include "wfun.mm"
include "ffun.mm"
include "funfvbrb.mm"
include "mp2b.mm"
include "sylib.mm"
include "breq2.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "isch3.mm"
include "sylanbrc.mm"

theorem occl
  let cA: class A
  let vf: setvar f
  let vx: setvar x


  assert |- ( A C_ ~H -> ( _|_ ` A ) e. CH )

  proof
    cA
    chil
    wss
    #
    cA
    cort
    cfv
    #
    csh
    wcel
    cn
    @1
    vf
    cv
    #
    wf
    #
    @2
    vx
    cv
    #
    chli
    wbr
    #
    vx
    @1
    wrex
    #
    wi
    #
    vf
    ccau
    wral
    @1
    cch
    wcel
    cA
    ocsh
    @0
    @7
    vf
    ccau
    @0
    @2
    ccau
    wcel
    #
    wa
    #
    @3
    @6
    @9
    @3
    wa
    #
    @2
    chli
    cfv
    #
    @1
    wcel
    #
    @2
    @11
    chli
    wbr
    #
    @6
    @10
    @12
    @11
    chil
    wcel
    #
    @11
    @4
    csp
    co
    cc0
    wceq
    #
    vx
    cA
    wral
    #
    @10
    @2
    chli
    cdm
    #
    wcel
    #
    @14
    @8
    @18
    @0
    @3
    @8
    @5
    vx
    chil
    wrex
    @18
    vx
    @2
    ax-hcompl
    @5
    @18
    vx
    chil
    @2
    @4
    chli
    vf
    vex
    vx
    vex
    breldm
    rexlimivw
    syl
    ad2antlr
    #
    @17
    chil
    @2
    chli
    hlimf
    ffvelrni
    syl
    @10
    @15
    vx
    cA
    @10
    @4
    cA
    wcel
    #
    wa
    cA
    @4
    @2
    @0
    @8
    @3
    @20
    simplll
    @0
    @8
    @3
    @20
    simpllr
    @9
    @3
    @20
    simplr
    @10
    @20
    simpr
    occllem
    ralrimiva
    @0
    @12
    @14
    @16
    wa
    wb
    @8
    @3
    vx
    @11
    cA
    ocel
    ad2antrr
    mpbir2and
    @10
    @18
    @13
    @19
    @17
    chil
    chli
    wf
    chli
    wfun
    @18
    @13
    wb
    hlimf
    @17
    chil
    chli
    ffun
    @2
    chli
    funfvbrb
    mp2b
    sylib
    @5
    @13
    vx
    @11
    @1
    @4
    @11
    @2
    chli
    breq2
    rspcev
    syl2anc
    ex
    ralrimiva
    vx
    vf
    @1
    isch3
    sylanbrc
end
