include "cdr.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "csubrg.mm"
include "cv.mm"
include "cinvr.mm"
include "c0g.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "csdrg.mm"
include "simpl.mm"
include "crg.mm"
include "drngring.mm"
include "cntzsubr.mm"
include "sylan.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "wne.mm"
include "eldifsn.mm"
include "cress.mm"
include "ccntz.mm"
include "cminusg.mm"
include "cui.mm"
include "eqid.mm"
include "cmgp.mm"
include "oveq1i.mm"
include "invrfval.mm"
include "isdrng.mm"
include "simprbi.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "ad2antrr.mm"
include "fveq1d.mm"
include "csubg.mm"
include "cgrp.mm"
include "drngmgp.mm"
include "ssdif.mm"
include "ad2antlr.mm"
include "cbs.mm"
include "difss.mm"
include "mgpbas.mm"
include "ressbas2.mm"
include "ax-mp.mm"
include "cntzsubg.mm"
include "syl2anc.mm"
include "cin.mm"
include "simpr.mm"
include "cntz2ss.mm"
include "sylancl.mm"
include "ssdifssd.mm"
include "sselda.mm"
include "cntzssv.mm"
include "mp1i.mm"
include "elind.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "difexg.mm"
include "resscntz.mm"
include "sylancr.mm"
include "eleqtrrd.mm"
include "subginvcl.mm"
include "eqeltrd.mm"
include "cplusg.mm"
include "mgpplusg.mm"
include "ressplusg.mm"
include "cntzi.mm"
include "sylan2br.mm"
include "anassrs.mm"
include "ad3antrrr.mm"
include "adantr.mm"
include "eldifi.mm"
include "adantl.mm"
include "sseldi.mm"
include "eldifsni.mm"
include "drnginvrcl.mm"
include "syl3anc.mm"
include "ringrz.mm"
include "ringlz.mm"
include "eqtr4d.mm"
include "pm2.61ne.mm"
include "ralrimiva.mm"
include "wb.mm"
include "simplr.mm"
include "cntzel.mm"
include "mpbird.mm"
include "issdrg2.mm"
include "syl3anbrc.mm"

theorem cntzsdrg
  let cB: class B
  let cR: class R
  let cS: class S
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  assume cntzsdrg.b: |- B = ( Base ` R )
  assume cntzsdrg.m: |- M = ( mulGrp ` R )
  assume cntzsdrg.z: |- Z = ( Cntz ` M )


  assert |- ( ( R e. DivRing /\ S C_ B ) -> ( Z ` S ) e. ( SubDRing ` R ) )

  proof
    cR
    cdr
    wcel
    #
    cS
    cB
    wss
    #
    wa
    #
    @0
    cS
    cZ
    cfv
    #
    cR
    csubrg
    cfv
    wcel
    #
    vx
    cv
    #
    cR
    cinvr
    cfv
    #
    cfv
    #
    @3
    wcel
    #
    vx
    @3
    cR
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wral
    @3
    cR
    csdrg
    cfv
    wcel
    @0
    @1
    simpl
    #
    @0
    cR
    crg
    wcel
    #
    @1
    @4
    cR
    drngring
    #
    cB
    cR
    cS
    cM
    cZ
    cntzsdrg.b
    cntzsdrg.m
    cntzsdrg.z
    cntzsubr
    sylan
    @2
    @8
    vx
    @11
    @2
    @5
    @11
    wcel
    #
    wa
    #
    @8
    @7
    vy
    cv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    @17
    @7
    @18
    co
    #
    wceq
    #
    vy
    cS
    wral
    #
    @16
    @21
    vy
    cS
    @16
    @17
    cS
    wcel
    #
    wa
    #
    @21
    @7
    @9
    @18
    co
    #
    @9
    @7
    @18
    co
    #
    wceq
    @17
    @9
    @17
    @9
    wceq
    @19
    @25
    @20
    @26
    @17
    @9
    @7
    @18
    oveq2
    @17
    @9
    @7
    @18
    oveq1
    eqeq12d
    @16
    @23
    @17
    @9
    wne
    #
    @21
    @23
    @27
    wa
    @16
    @17
    cS
    @10
    cdif
    #
    wcel
    #
    @21
    @17
    cS
    @9
    eldifsn
    @16
    @7
    @28
    cM
    cB
    @10
    cdif
    #
    cress
    co
    #
    ccntz
    cfv
    #
    cfv
    #
    wcel
    @29
    @21
    @16
    @7
    @5
    @31
    cminusg
    cfv
    #
    cfv
    #
    @33
    @16
    @5
    @6
    @34
    @0
    @6
    @34
    wceq
    @1
    @15
    @0
    @6
    cM
    cR
    cui
    cfv
    #
    cress
    co
    #
    cminusg
    cfv
    @34
    cR
    @36
    @37
    @6
    @36
    eqid
    #
    cM
    cR
    cmgp
    cfv
    #
    @36
    cress
    cntzsdrg.m
    oveq1i
    @6
    eqid
    #
    invrfval
    @0
    @37
    @31
    cminusg
    @0
    @36
    @30
    cM
    cress
    @0
    @13
    @36
    @30
    wceq
    cB
    cR
    @36
    @9
    cntzsdrg.b
    @38
    @9
    eqid
    #
    isdrng
    simprbi
    oveq2d
    fveq2d
    syl5eq
    ad2antrr
    fveq1d
    @16
    @33
    @31
    csubg
    cfv
    wcel
    #
    @5
    @33
    wcel
    @35
    @33
    wcel
    @16
    @31
    cgrp
    wcel
    #
    @28
    @30
    wss
    #
    @42
    @0
    @43
    @1
    @15
    cB
    cR
    @31
    @9
    cntzsdrg.b
    @41
    cM
    @39
    @30
    cress
    cntzsdrg.m
    oveq1i
    drngmgp
    ad2antrr
    @1
    @44
    @0
    @15
    cS
    cB
    @10
    ssdif
    ad2antlr
    #
    @30
    @28
    @31
    @32
    @30
    cB
    wss
    @30
    @31
    cbs
    cfv
    wceq
    cB
    @10
    difss
    @30
    cB
    @31
    cM
    @31
    eqid
    #
    cB
    cR
    cM
    cntzsdrg.m
    cntzsdrg.b
    mgpbas
    #
    ressbas2
    ax-mp
    @32
    eqid
    #
    cntzsubg
    syl2anc
    @16
    @5
    @28
    cZ
    cfv
    #
    @30
    cin
    #
    @33
    @16
    @49
    @30
    @5
    @2
    @11
    @49
    @5
    @2
    @3
    @49
    @10
    @2
    @1
    @28
    cS
    wss
    @3
    @49
    wss
    @0
    @1
    simpr
    cS
    @10
    difss
    cB
    cS
    @28
    cM
    cZ
    @47
    cntzsdrg.z
    cntz2ss
    sylancl
    ssdifssd
    sselda
    @2
    @11
    @30
    @5
    @3
    cB
    wss
    @11
    @30
    wss
    @2
    cB
    cS
    cM
    cZ
    @47
    cntzsdrg.z
    cntzssv
    #
    @3
    cB
    @10
    ssdif
    mp1i
    sselda
    elind
    @16
    @30
    cvv
    wcel
    #
    @44
    @33
    @50
    wceq
    cB
    cvv
    wcel
    @52
    cB
    cR
    cbs
    cfv
    cvv
    cntzsdrg.b
    cR
    cbs
    fvex
    eqeltri
    cB
    @10
    cvv
    difexg
    ax-mp
    #
    @45
    @30
    @28
    cM
    @31
    cvv
    @32
    cZ
    @46
    cntzsdrg.z
    @48
    resscntz
    sylancr
    eleqtrrd
    @33
    @31
    @34
    @5
    @34
    eqid
    subginvcl
    syl2anc
    eqeltrd
    @18
    @28
    @31
    @7
    @17
    @32
    @52
    @18
    @31
    cplusg
    cfv
    wceq
    @53
    @30
    @18
    cM
    @31
    cvv
    @46
    cR
    @18
    cM
    cntzsdrg.m
    @18
    eqid
    #
    mgpplusg
    #
    ressplusg
    ax-mp
    @48
    cntzi
    sylan
    sylan2br
    anassrs
    @24
    @25
    @9
    @26
    @24
    @13
    @7
    cB
    wcel
    #
    @25
    @9
    wceq
    @0
    @13
    @1
    @15
    @23
    @14
    ad3antrrr
    #
    @16
    @56
    @23
    @16
    @0
    @5
    cB
    wcel
    @5
    @9
    wne
    #
    @56
    @2
    @0
    @15
    @12
    adantr
    @16
    @3
    cB
    @5
    @51
    @15
    @5
    @3
    wcel
    @2
    @5
    @3
    @10
    eldifi
    adantl
    sseldi
    @15
    @58
    @2
    @5
    @3
    @9
    eldifsni
    adantl
    cB
    cR
    @6
    @5
    @9
    cntzsdrg.b
    @41
    @40
    drnginvrcl
    syl3anc
    #
    adantr
    #
    cB
    cR
    @18
    @7
    @9
    cntzsdrg.b
    @54
    @41
    ringrz
    syl2anc
    @24
    @13
    @56
    @26
    @9
    wceq
    @57
    @60
    cB
    cR
    @18
    @7
    @9
    cntzsdrg.b
    @54
    @41
    ringlz
    syl2anc
    eqtr4d
    pm2.61ne
    ralrimiva
    @16
    @1
    @56
    @8
    @22
    wb
    @0
    @1
    @15
    simplr
    @59
    vy
    cB
    @18
    cS
    cM
    @7
    cZ
    @47
    @55
    cntzsdrg.z
    cntzel
    syl2anc
    mpbird
    ralrimiva
    vx
    cR
    @3
    @6
    @9
    @40
    @41
    issdrg2
    syl3anbrc
end
