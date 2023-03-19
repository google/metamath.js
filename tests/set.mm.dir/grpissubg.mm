include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cplusg.mm"
include "cfv.mm"
include "cxp.mm"
include "cres.mm"
include "wceq.mm"
include "csubg.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "cminusg.mm"
include "simpl.mm"
include "adantl.mm"
include "grpbn0.mm"
include "ad2antlr.mm"
include "ovres.mm"
include "adantll.mm"
include "simplr.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "eqid.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "wb.mm"
include "oveq.mm"
include "eqcomd.mm"
include "eleq1d.mm"
include "mpbird.mm"
include "eqeltrrd.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "cbs.mm"
include "sseq2i.mm"
include "biimpi.mm"
include "eqtr3d.mm"
include "ralrimivva.mm"
include "grpinvssd.mm"
include "imp.mm"
include "wi.mm"
include "grpinvcl.mm"
include "ex.mm"
include "jca.mm"
include "w3a.mm"
include "issubg2.mm"
include "mpbir3and.mm"

theorem grpissubg
  let cB: class B
  let cS: class S
  let cG: class G
  let cH: class H
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  assume grpissubg.b: |- B = ( Base ` G )
  assume grpissubg.s: |- S = ( Base ` H )


  assert |- ( ( G e. Grp /\ H e. Grp ) -> ( ( S C_ B /\ ( +g ` H ) = ( ( +g ` G ) |` ( S X. S ) ) ) -> S e. ( SubGrp ` G ) ) )

  proof
    cG
    cgrp
    wcel
    #
    cH
    cgrp
    wcel
    #
    wa
    #
    cS
    cB
    wss
    #
    cH
    cplusg
    cfv
    #
    cG
    cplusg
    cfv
    #
    cS
    cS
    cxp
    cres
    #
    wceq
    #
    wa
    #
    cS
    cG
    csubg
    cfv
    wcel
    #
    @2
    @8
    wa
    #
    @9
    @3
    cS
    c0
    wne
    #
    va
    cv
    #
    vb
    cv
    #
    @5
    co
    #
    cS
    wcel
    #
    vb
    cS
    wral
    #
    @12
    cG
    cminusg
    cfv
    #
    cfv
    #
    cS
    wcel
    #
    wa
    #
    va
    cS
    wral
    #
    @8
    @3
    @2
    @3
    @7
    simpl
    adantl
    @1
    @11
    @0
    @8
    cS
    cH
    grpissubg.s
    grpbn0
    ad2antlr
    @10
    @20
    va
    cS
    @10
    @12
    cS
    wcel
    #
    wa
    #
    @16
    @19
    @23
    @15
    vb
    cS
    @23
    @13
    cS
    wcel
    #
    wa
    #
    @12
    @13
    @6
    co
    #
    @14
    cS
    @22
    @24
    @26
    @14
    wceq
    @10
    @12
    @13
    cS
    cS
    @5
    ovres
    adantll
    @25
    @26
    cS
    wcel
    #
    @12
    @13
    @4
    co
    #
    cS
    wcel
    #
    @25
    @1
    @22
    @24
    @29
    @10
    @1
    @22
    @24
    @0
    @1
    @8
    simplr
    #
    ad2antrr
    @10
    @22
    @24
    simplr
    @23
    @24
    simpr
    cS
    @4
    cH
    @12
    @13
    grpissubg.s
    @4
    eqid
    grpcl
    syl3anc
    @10
    @27
    @29
    wb
    #
    @22
    @24
    @8
    @31
    @2
    @7
    @31
    @3
    @7
    @26
    @28
    cS
    @7
    @28
    @26
    @12
    @13
    @4
    @6
    oveq
    eqcomd
    eleq1d
    adantl
    adantl
    ad2antrr
    mpbird
    eqeltrrd
    ralrimiva
    @23
    @12
    cH
    cminusg
    cfv
    #
    cfv
    #
    @18
    cS
    @10
    @22
    @33
    @18
    wceq
    @10
    vx
    vy
    cS
    cH
    cG
    @12
    @2
    @0
    @8
    @0
    @1
    simpl
    adantr
    @30
    grpissubg.s
    @8
    cS
    cG
    cbs
    cfv
    #
    wss
    #
    @2
    @3
    @35
    @7
    @3
    @35
    cB
    @34
    cS
    grpissubg.b
    sseq2i
    biimpi
    adantr
    adantl
    @10
    vx
    cv
    #
    vy
    cv
    #
    @5
    co
    #
    @36
    @37
    @4
    co
    #
    wceq
    vx
    vy
    cS
    cS
    @10
    @36
    cS
    wcel
    @37
    cS
    wcel
    wa
    #
    wa
    @36
    @37
    @6
    co
    #
    @38
    @39
    @40
    @41
    @38
    wceq
    @10
    @36
    @37
    cS
    cS
    @5
    ovres
    adantl
    @8
    @41
    @39
    wceq
    @2
    @40
    @8
    @39
    @41
    @7
    @39
    @41
    wceq
    @3
    @36
    @37
    @4
    @6
    oveq
    adantl
    eqcomd
    ad2antlr
    eqtr3d
    ralrimivva
    grpinvssd
    imp
    @10
    @22
    @33
    cS
    wcel
    #
    @1
    @22
    @42
    wi
    @0
    @8
    @1
    @22
    @42
    cS
    cH
    @32
    @12
    grpissubg.s
    @32
    eqid
    grpinvcl
    ex
    ad2antlr
    imp
    eqeltrrd
    jca
    ralrimiva
    @0
    @9
    @3
    @11
    @21
    w3a
    wb
    @1
    @8
    va
    vb
    cB
    @5
    cS
    cG
    @17
    grpissubg.b
    @5
    eqid
    @17
    eqid
    issubg2
    ad2antrr
    mpbir3and
    ex
end
