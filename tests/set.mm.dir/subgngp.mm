include "cngp.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "wa.mm"
include "cgrp.mm"
include "cmt.mm"
include "cv.mm"
include "cds.mm"
include "co.mm"
include "csg.mm"
include "cnm.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "subggrp.mm"
include "adantl.mm"
include "cress.mm"
include "ngpms.mm"
include "ressms.mm"
include "sylan.mm"
include "syl5eqel.mm"
include "simplr.mm"
include "simprl.mm"
include "subgbas.mm"
include "ad2antlr.mm"
include "eleqtrrd.mm"
include "simprr.mm"
include "eqid.mm"
include "subgsub.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "ressds.mm"
include "oveqd.mm"
include "simpll.mm"
include "wss.mm"
include "subgss.mm"
include "sseldd.mm"
include "ngpds.mm"
include "eqtr3d.mm"
include "grpsubcl.mm"
include "3expb.mm"
include "subgnm2.mm"
include "syl2anc.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "isngp3.mm"
include "syl3anbrc.mm"

theorem subgngp
  let cA: class A
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume subgngp.h: |- H = ( G |`s A )


  assert |- ( ( G e. NrmGrp /\ A e. ( SubGrp ` G ) ) -> H e. NrmGrp )

  proof
    cG
    cngp
    wcel
    #
    cA
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
    cH
    cmt
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cH
    cds
    cfv
    #
    co
    #
    @5
    @6
    cH
    csg
    cfv
    #
    co
    #
    cH
    cnm
    cfv
    #
    cfv
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
    @14
    wral
    cH
    cngp
    wcel
    @2
    @4
    @0
    cA
    cG
    cH
    subgngp.h
    subggrp
    adantl
    #
    @3
    cH
    cG
    cA
    cress
    co
    #
    cmt
    subgngp.h
    @0
    cG
    cmt
    wcel
    @2
    @16
    cmt
    wcel
    cG
    ngpms
    cA
    cG
    @1
    ressms
    sylan
    syl5eqel
    @3
    @13
    vx
    vy
    @14
    @14
    @3
    @5
    @14
    wcel
    #
    @6
    @14
    wcel
    #
    wa
    #
    wa
    #
    @5
    @6
    cG
    csg
    cfv
    #
    co
    #
    cG
    cnm
    cfv
    #
    cfv
    #
    @10
    @23
    cfv
    #
    @8
    @12
    @20
    @22
    @10
    @23
    @20
    @2
    @5
    cA
    wcel
    @6
    cA
    wcel
    @22
    @10
    wceq
    @0
    @2
    @19
    simplr
    #
    @20
    @5
    @14
    cA
    @3
    @17
    @18
    simprl
    @2
    cA
    @14
    wceq
    @0
    @19
    cA
    cG
    cH
    subgngp.h
    subgbas
    ad2antlr
    #
    eleqtrrd
    #
    @20
    @6
    @14
    cA
    @3
    @17
    @18
    simprr
    @27
    eleqtrrd
    #
    cA
    cG
    cH
    @21
    @9
    @5
    @6
    @21
    eqid
    #
    subgngp.h
    @9
    eqid
    #
    subgsub
    syl3anc
    fveq2d
    @20
    @5
    @6
    cG
    cds
    cfv
    #
    co
    #
    @8
    @24
    @20
    @32
    @7
    @5
    @6
    @2
    @32
    @7
    wceq
    @0
    @19
    cA
    @32
    cG
    cH
    @1
    subgngp.h
    @32
    eqid
    #
    ressds
    ad2antlr
    oveqd
    @20
    @0
    @5
    cG
    cbs
    cfv
    #
    wcel
    @6
    @35
    wcel
    @33
    @24
    wceq
    @0
    @2
    @19
    simpll
    @20
    cA
    @35
    @5
    @2
    cA
    @35
    wss
    @0
    @19
    @35
    cA
    cG
    @35
    eqid
    #
    subgss
    ad2antlr
    #
    @28
    sseldd
    @20
    cA
    @35
    @6
    @37
    @29
    sseldd
    @5
    @6
    @32
    cG
    @21
    @23
    @35
    @23
    eqid
    #
    @36
    @30
    @34
    ngpds
    syl3anc
    eqtr3d
    @20
    @2
    @10
    cA
    wcel
    @12
    @25
    wceq
    @26
    @20
    @10
    @14
    cA
    @3
    @4
    @19
    @10
    @14
    wcel
    #
    @15
    @4
    @17
    @18
    @39
    @14
    cH
    @9
    @5
    @6
    @14
    eqid
    #
    @31
    grpsubcl
    3expb
    sylan
    @27
    eleqtrrd
    cA
    cG
    cH
    @11
    @23
    @10
    subgngp.h
    @38
    @11
    eqid
    #
    subgnm2
    syl2anc
    3eqtr4d
    ralrimivva
    vx
    vy
    @7
    cH
    @9
    @11
    @14
    @41
    @31
    @7
    eqid
    @40
    isngp3
    syl3anbrc
end
