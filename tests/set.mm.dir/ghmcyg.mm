include "ccyg.mm"
include "wcel.mm"
include "cz.mm"
include "cv.mm"
include "cmg.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "wrex.mm"
include "cghm.mm"
include "wfo.mm"
include "wa.mm"
include "cgrp.mm"
include "eqid.mm"
include "iscyg.mm"
include "simprbi.mm"
include "ghmgrp2.mm"
include "ad2antrr.mm"
include "wf.mm"
include "fof.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "simplr.mm"
include "wb.mm"
include "foeq2.mm"
include "ad2antll.mm"
include "mpbird.mm"
include "foelrn.mm"
include "sylan.mm"
include "cvv.mm"
include "wral.mm"
include "ovex.mm"
include "rgenw.mm"
include "oveq1.mm"
include "cbvmptv.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "rexrnmpt.mm"
include "ax-mp.mm"
include "sylib.mm"
include "simp-4l.mm"
include "simpr.mm"
include "ghmmulg.mm"
include "syl3anc.mm"
include "rexbidva.mm"
include "mpbid.mm"
include "iscygd.mm"
include "rexlimdvaa.mm"
include "syl5.mm"

theorem ghmcyg
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cH: class H
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  let vb: setvar b
  let cE: class E
  assume cygctb.1: |- B = ( Base ` G )
  assume ghmcyg.1: |- C = ( Base ` H )


  assert |- ( ( F e. ( G GrpHom H ) /\ F : B -onto-> C ) -> ( G e. CycGrp -> H e. CycGrp ) )

  proof
    cG
    ccyg
    wcel
    #
    vn
    cz
    vn
    cv
    #
    vx
    cv
    #
    cG
    cmg
    cfv
    #
    co
    #
    cmpt
    #
    crn
    #
    cB
    wceq
    #
    vx
    cB
    wrex
    #
    cF
    cG
    cH
    cghm
    co
    wcel
    #
    cB
    cC
    cF
    wfo
    #
    wa
    #
    cH
    ccyg
    wcel
    #
    @0
    cG
    cgrp
    wcel
    @8
    vx
    cB
    @3
    vn
    cG
    cygctb.1
    @3
    eqid
    #
    iscyg
    simprbi
    @11
    @7
    @12
    vx
    cB
    @11
    @2
    cB
    wcel
    #
    @7
    wa
    #
    wa
    #
    vy
    cC
    cH
    cmg
    cfv
    #
    vm
    cH
    @2
    cF
    cfv
    #
    ghmcyg.1
    @17
    eqid
    #
    @9
    cH
    cgrp
    wcel
    @10
    @15
    cG
    cH
    cF
    ghmgrp2
    ad2antrr
    @16
    cB
    cC
    @2
    cF
    @10
    cB
    cC
    cF
    wf
    @9
    @15
    cB
    cC
    cF
    fof
    ad2antlr
    @11
    @14
    @7
    simprl
    #
    ffvelrnd
    @16
    vy
    cv
    #
    cC
    wcel
    #
    wa
    #
    @21
    vm
    cv
    #
    @2
    @3
    co
    #
    cF
    cfv
    #
    wceq
    #
    vm
    cz
    wrex
    #
    @21
    @24
    @18
    @17
    co
    #
    wceq
    #
    vm
    cz
    wrex
    @23
    @21
    vz
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vz
    @6
    wrex
    #
    @28
    @16
    @6
    cC
    cF
    wfo
    #
    @22
    @34
    @16
    @35
    @10
    @9
    @10
    @15
    simplr
    @7
    @35
    @10
    wb
    @11
    @14
    @6
    cB
    cC
    cF
    foeq2
    ad2antll
    mpbird
    vz
    @6
    cC
    @21
    cF
    foelrn
    sylan
    @25
    cvv
    wcel
    #
    vm
    cz
    wral
    @34
    @28
    wb
    @36
    vm
    cz
    @24
    @2
    @3
    ovex
    rgenw
    @33
    @27
    vm
    vz
    cz
    @25
    @5
    cvv
    vn
    vm
    cz
    @4
    @25
    @1
    @24
    @2
    @3
    oveq1
    cbvmptv
    @31
    @25
    wceq
    @32
    @26
    @21
    @31
    @25
    cF
    fveq2
    eqeq2d
    rexrnmpt
    ax-mp
    sylib
    @23
    @27
    @30
    vm
    cz
    @23
    @24
    cz
    wcel
    #
    wa
    #
    @26
    @29
    @21
    @38
    @9
    @37
    @14
    @26
    @29
    wceq
    @9
    @10
    @15
    @22
    @37
    simp-4l
    @23
    @37
    simpr
    @16
    @14
    @22
    @37
    @20
    ad2antrr
    cB
    @3
    @17
    cF
    cG
    cH
    @24
    @2
    cygctb.1
    @13
    @19
    ghmmulg
    syl3anc
    eqeq2d
    rexbidva
    mpbid
    iscygd
    rexlimdvaa
    syl5
end
