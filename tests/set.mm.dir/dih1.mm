include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wrel.mm"
include "wceq.mm"
include "dihvalrel.mm"
include "cltrn.mm"
include "ctendo.mm"
include "cxp.mm"
include "relxp.mm"
include "eqid.mm"
include "dvhvbase.mm"
include "releqd.mm"
include "mpbiri.mm"
include "id.mm"
include "cv.mm"
include "coc.mm"
include "crio.mm"
include "ccnv.mm"
include "ccom.mm"
include "ctrl.mm"
include "cple.mm"
include "wbr.mm"
include "cop.mm"
include "cops.mm"
include "cbs.mm"
include "hlop.mm"
include "ad2antrr.mm"
include "simpl.mm"
include "simprl.mm"
include "simprr.mm"
include "catm.mm"
include "wn.mm"
include "lhpocnel.mm"
include "adantr.mm"
include "ltrniotacl.mm"
include "syl3anc.mm"
include "tendocl.mm"
include "ltrncnv.mm"
include "syldan.mm"
include "ltrnco.mm"
include "trlcl.mm"
include "ople1.mm"
include "syl2anc.mm"
include "ex.mm"
include "pm4.71d.mm"
include "eleq2d.mm"
include "opelxp.mm"
include "syl6bb.mm"
include "cmee.mm"
include "co.mm"
include "cjn.mm"
include "wb.mm"
include "op1cl.mm"
include "syl.mm"
include "cpo.mm"
include "ccvr.mm"
include "hlpos.mm"
include "lhpbase.mm"
include "adantl.mm"
include "lhp1cvr.mm"
include "cvrnle.mm"
include "syl31anc.mm"
include "col.mm"
include "hlol.mm"
include "olm12.mm"
include "syl2an.mm"
include "oveq2d.mm"
include "clat.mm"
include "hllat.mm"
include "opoccl.mm"
include "latjcom.mm"
include "opexmid.mm"
include "3eqtrd.mm"
include "vex.mm"
include "dihopelvalc.mm"
include "syl122anc.mm"
include "3bitr4rd.mm"
include "eqrelrdv2.mm"
include "syl21anc.mm"

theorem dih1
  let cU: class U
  let c.1: class .1.
  let cH: class H
  let cI: class I
  let cK: class K
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  let vs: setvar s
  assume dih1.m: |- .1. = ( 1. ` K )
  assume dih1.h: |- H = ( LHyp ` K )
  assume dih1.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dih1.u: |- U = ( ( DVecH ` K ) ` W )
  assume dih1.v: |- V = ( Base ` U )


  assert |- ( ( K e. HL /\ W e. H ) -> ( I ` .1. ) = V )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    c.1
    cI
    cfv
    #
    wrel
    cV
    wrel
    #
    @2
    @3
    cV
    wceq
    cH
    cI
    cK
    cW
    c.1
    dih1.h
    dih1.i
    dihvalrel
    @2
    @4
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cW
    cK
    ctendo
    cfv
    cfv
    #
    cxp
    #
    wrel
    @5
    @6
    relxp
    @2
    cV
    @7
    @5
    cU
    @6
    cH
    cK
    cV
    cW
    chlt
    dih1.h
    @5
    eqid
    #
    @6
    eqid
    #
    dih1.u
    dih1.v
    dvhvbase
    #
    releqd
    mpbiri
    @2
    id
    #
    @2
    vf
    vs
    @3
    cV
    @2
    vf
    cv
    #
    @5
    wcel
    #
    vs
    cv
    #
    @6
    wcel
    #
    wa
    #
    @16
    @12
    cW
    cK
    coc
    cfv
    #
    cfv
    #
    vg
    cv
    cfv
    @18
    wceq
    vg
    @5
    crio
    #
    @14
    cfv
    #
    ccnv
    #
    ccom
    #
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cfv
    #
    c.1
    cK
    cple
    cfv
    #
    wbr
    #
    wa
    #
    @12
    @14
    cop
    #
    cV
    wcel
    #
    @28
    @3
    wcel
    #
    @2
    @16
    @26
    @2
    @16
    @26
    @2
    @16
    wa
    #
    cK
    cops
    wcel
    #
    @24
    cK
    cbs
    cfv
    #
    wcel
    #
    @26
    @0
    @32
    @1
    @16
    cK
    hlop
    #
    ad2antrr
    @2
    @16
    @22
    @5
    wcel
    #
    @34
    @31
    @2
    @13
    @21
    @5
    wcel
    #
    @36
    @2
    @16
    simpl
    #
    @2
    @13
    @15
    simprl
    @2
    @16
    @20
    @5
    wcel
    #
    @37
    @31
    @2
    @15
    @19
    @5
    wcel
    #
    @39
    @38
    @2
    @13
    @15
    simprr
    @31
    @2
    @18
    cK
    catm
    cfv
    #
    wcel
    @18
    cW
    @25
    wbr
    wn
    wa
    #
    @42
    @40
    @38
    @2
    @42
    @16
    @41
    cH
    cK
    @25
    @17
    cW
    @25
    eqid
    #
    @17
    eqid
    #
    @41
    eqid
    #
    dih1.h
    lhpocnel
    #
    adantr
    #
    @47
    @41
    @18
    @18
    @5
    vg
    @19
    cH
    cK
    @25
    cW
    @43
    @45
    dih1.h
    @8
    @19
    eqid
    #
    ltrniotacl
    syl3anc
    @14
    @5
    @6
    @19
    cH
    cK
    chlt
    cW
    dih1.h
    @8
    @9
    tendocl
    syl3anc
    @5
    @20
    cH
    cK
    cW
    dih1.h
    @8
    ltrncnv
    syldan
    @5
    @12
    @21
    cH
    cK
    cW
    dih1.h
    @8
    ltrnco
    syl3anc
    @33
    @23
    @5
    @22
    cH
    cK
    cW
    @33
    eqid
    #
    dih1.h
    @8
    @23
    eqid
    #
    trlcl
    syldan
    @33
    c.1
    cK
    @25
    @24
    @49
    @43
    dih1.m
    ople1
    syl2anc
    ex
    pm4.71d
    @2
    @29
    @28
    @7
    wcel
    @16
    @2
    cV
    @7
    @28
    @10
    eleq2d
    @12
    @14
    @5
    @6
    opelxp
    syl6bb
    @2
    @2
    c.1
    @33
    wcel
    #
    c.1
    cW
    @25
    wbr
    wn
    #
    @42
    @18
    c.1
    cW
    cK
    cmee
    cfv
    #
    co
    #
    cK
    cjn
    cfv
    #
    co
    #
    c.1
    wceq
    @30
    @27
    wb
    @11
    @2
    @32
    @51
    @0
    @32
    @1
    @35
    adantr
    @33
    c.1
    cK
    @49
    dih1.m
    op1cl
    syl
    #
    @2
    cK
    cpo
    wcel
    #
    cW
    @33
    wcel
    #
    @51
    cW
    c.1
    cK
    ccvr
    cfv
    #
    wbr
    @52
    @0
    @58
    @1
    cK
    hlpos
    adantr
    @1
    @59
    @0
    @33
    cH
    cK
    cW
    @49
    dih1.h
    lhpbase
    #
    adantl
    #
    @57
    chlt
    @60
    c.1
    cH
    cK
    cW
    dih1.m
    @60
    eqid
    #
    dih1.h
    lhp1cvr
    @33
    @60
    cK
    @25
    cW
    c.1
    @49
    @43
    @63
    cvrnle
    syl31anc
    @46
    @2
    @56
    @18
    cW
    @55
    co
    #
    cW
    @18
    @55
    co
    #
    c.1
    @2
    @54
    cW
    @18
    @55
    @0
    cK
    col
    wcel
    @59
    @54
    cW
    wceq
    @1
    cK
    hlol
    @61
    @33
    c.1
    cK
    @53
    cW
    @49
    @53
    eqid
    #
    dih1.m
    olm12
    syl2an
    oveq2d
    @2
    cK
    clat
    wcel
    #
    @18
    @33
    wcel
    #
    @59
    @64
    @65
    wceq
    @0
    @67
    @1
    cK
    hllat
    adantr
    @0
    @32
    @59
    @68
    @1
    @35
    @61
    @33
    cK
    @17
    cW
    @49
    @44
    opoccl
    syl2an
    @62
    @33
    @55
    cK
    @18
    cW
    @49
    @55
    eqid
    #
    latjcom
    syl3anc
    @0
    @32
    @59
    @65
    c.1
    wceq
    @1
    @35
    @61
    @33
    c.1
    @55
    cK
    @17
    cW
    @49
    @44
    @69
    dih1.m
    opexmid
    syl2an
    3eqtrd
    @41
    @33
    @18
    @18
    @23
    @14
    @5
    vg
    @6
    @12
    @19
    cH
    cI
    @55
    cK
    @25
    @53
    cW
    c.1
    @49
    @43
    @69
    @66
    @45
    dih1.h
    @18
    eqid
    @8
    @50
    @9
    dih1.i
    @48
    vf
    vex
    vs
    vex
    dihopelvalc
    syl122anc
    3bitr4rd
    eqrelrdv2
    syl21anc
end
