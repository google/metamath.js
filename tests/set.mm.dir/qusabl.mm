include "cabl.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "wa.mm"
include "cgrp.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "cnsg.mm"
include "ablnsg.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "qusgrp.mm"
include "syl.mm"
include "cqg.mm"
include "cec.mm"
include "wrex.mm"
include "cqs.mm"
include "vex.mm"
include "elqs.mm"
include "cvv.mm"
include "cqus.mm"
include "a1i.mm"
include "eqidd.mm"
include "ovexd.mm"
include "simpl.mm"
include "qusbas.mm"
include "syl5bbr.mm"
include "anbi12d.mm"
include "reeanv.mm"
include "eqid.mm"
include "ablcom.mm"
include "3expb.mm"
include "adantlr.mm"
include "eceq1d.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "qusadd.mm"
include "syl3anc.mm"
include "3eqtr4d.mm"
include "oveq12.mm"
include "ancoms.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "sylbird.mm"
include "ralrimivv.mm"
include "isabl2.mm"
include "sylanbrc.mm"

theorem qusabl
  let cS: class S
  let cG: class G
  let cH: class H
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  assume qusabl.h: |- H = ( G /s ( G ~QG S ) )


  assert |- ( ( G e. Abel /\ S e. ( SubGrp ` G ) ) -> H e. Abel )

  proof
    cG
    cabl
    wcel
    #
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    wa
    #
    cH
    cgrp
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cH
    cplusg
    cfv
    #
    co
    #
    @6
    @5
    @7
    co
    #
    wceq
    #
    vy
    cH
    cbs
    cfv
    #
    wral
    vx
    @11
    wral
    cH
    cabl
    wcel
    @3
    cS
    cG
    cnsg
    cfv
    #
    wcel
    #
    @4
    @0
    @13
    @2
    @0
    @12
    @1
    cS
    cG
    ablnsg
    eleq2d
    biimpar
    #
    cS
    cG
    cH
    qusabl.h
    qusgrp
    syl
    @3
    @10
    vx
    vy
    @11
    @11
    @3
    @5
    @11
    wcel
    #
    @6
    @11
    wcel
    #
    wa
    @5
    va
    cv
    #
    cG
    cS
    cqg
    co
    #
    cec
    #
    wceq
    #
    va
    cG
    cbs
    cfv
    #
    wrex
    #
    @6
    vb
    cv
    #
    @18
    cec
    #
    wceq
    #
    vb
    @21
    wrex
    #
    wa
    #
    @10
    @3
    @22
    @15
    @26
    @16
    @22
    @5
    @21
    @18
    cqs
    #
    wcel
    @3
    @15
    va
    @21
    @5
    @18
    vx
    vex
    elqs
    @3
    @28
    @11
    @5
    @3
    @18
    cG
    cH
    @21
    cvv
    cabl
    cH
    cG
    @18
    cqus
    co
    wceq
    @3
    qusabl.h
    a1i
    @3
    @21
    eqidd
    @3
    cG
    cS
    cqg
    ovexd
    @0
    @2
    simpl
    qusbas
    #
    eleq2d
    syl5bbr
    @26
    @6
    @28
    wcel
    @3
    @16
    vb
    @21
    @6
    @18
    vy
    vex
    elqs
    @3
    @28
    @11
    @6
    @29
    eleq2d
    syl5bbr
    anbi12d
    @27
    @20
    @25
    wa
    #
    vb
    @21
    wrex
    va
    @21
    wrex
    @3
    @10
    @20
    @25
    va
    vb
    @21
    @21
    reeanv
    @3
    @30
    @10
    va
    vb
    @21
    @21
    @3
    @17
    @21
    wcel
    #
    @23
    @21
    wcel
    #
    wa
    #
    wa
    #
    @10
    @30
    @19
    @24
    @7
    co
    #
    @24
    @19
    @7
    co
    #
    wceq
    @34
    @17
    @23
    cG
    cplusg
    cfv
    #
    co
    #
    @18
    cec
    #
    @23
    @17
    @37
    co
    #
    @18
    cec
    #
    @35
    @36
    @34
    @38
    @40
    @18
    @0
    @33
    @38
    @40
    wceq
    #
    @2
    @0
    @31
    @32
    @42
    @21
    @37
    cG
    @17
    @23
    @21
    eqid
    #
    @37
    eqid
    #
    ablcom
    3expb
    adantlr
    eceq1d
    @34
    @13
    @31
    @32
    @35
    @39
    wceq
    @3
    @13
    @33
    @14
    adantr
    #
    @3
    @31
    @32
    simprl
    #
    @3
    @31
    @32
    simprr
    #
    @37
    @7
    cS
    cG
    cH
    @21
    @17
    @23
    qusabl.h
    @43
    @44
    @7
    eqid
    #
    qusadd
    syl3anc
    @34
    @13
    @32
    @31
    @36
    @41
    wceq
    @45
    @47
    @46
    @37
    @7
    cS
    cG
    cH
    @21
    @23
    @17
    qusabl.h
    @43
    @44
    @48
    qusadd
    syl3anc
    3eqtr4d
    @30
    @8
    @35
    @9
    @36
    @5
    @19
    @6
    @24
    @7
    oveq12
    @25
    @20
    @9
    @36
    wceq
    @6
    @24
    @5
    @19
    @7
    oveq12
    ancoms
    eqeq12d
    syl5ibrcom
    rexlimdvva
    syl5bir
    sylbird
    ralrimivv
    vx
    vy
    @11
    @7
    cH
    @11
    eqid
    @48
    isabl2
    sylanbrc
end
