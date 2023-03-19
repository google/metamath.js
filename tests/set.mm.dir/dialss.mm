include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "ctendo.mm"
include "cfv.mm"
include "cplusg.mm"
include "cvsca.mm"
include "csca.mm"
include "cltrn.mm"
include "eqidd.mm"
include "cbs.mm"
include "wceq.mm"
include "eqid.mm"
include "dvabase.mm"
include "eqcomd.mm"
include "adantr.mm"
include "dvavbase.mm"
include "clss.mm"
include "a1i.mm"
include "diass.mm"
include "dian0.mm"
include "cv.mm"
include "w3a.mm"
include "co.mm"
include "ccom.mm"
include "simpll.mm"
include "simpr1.mm"
include "simplr.mm"
include "simpr2.mm"
include "diael.mm"
include "syl3anc.mm"
include "dvavsca.mm"
include "syl12anc.mm"
include "oveq1d.mm"
include "tendocl.mm"
include "simpr3.mm"
include "dvavadd.mm"
include "eqtrd.mm"
include "ctrl.mm"
include "ltrnco.mm"
include "cjn.mm"
include "clat.mm"
include "hllat.mm"
include "ad3antrrr.mm"
include "trlcl.mm"
include "syl2anc.mm"
include "latjcl.mm"
include "simplrl.mm"
include "trlco.mm"
include "tendotp.mm"
include "diatrl.mm"
include "lattrd.mm"
include "wb.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "diaelval.mm"
include "mpbir2and.mm"
include "eqeltrd.mm"
include "islssd.mm"

theorem dialss
  let cB: class B
  let cS: class S
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  assume dialss.b: |- B = ( Base ` K )
  assume dialss.l: |- .<_ = ( le ` K )
  assume dialss.h: |- H = ( LHyp ` K )
  assume dialss.u: |- U = ( ( DVecA ` K ) ` W )
  assume dialss.i: |- I = ( ( DIsoA ` K ) ` W )
  assume dialss.s: |- S = ( LSubSp ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ X .<_ W ) ) -> ( I ` X ) e. S )

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
    cX
    cB
    wcel
    #
    cX
    cW
    c.le
    wbr
    #
    wa
    #
    wa
    #
    vx
    cW
    cK
    ctendo
    cfv
    cfv
    #
    cU
    cplusg
    cfv
    #
    cS
    cU
    cvsca
    cfv
    #
    cX
    cI
    cfv
    #
    cU
    csca
    cfv
    #
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cU
    va
    vb
    @6
    @11
    eqidd
    @2
    @7
    @11
    cbs
    cfv
    #
    wceq
    @5
    @2
    @13
    @7
    @13
    cU
    @7
    @11
    cH
    cK
    cW
    chlt
    dialss.h
    @7
    eqid
    #
    dialss.u
    @11
    eqid
    @13
    eqid
    dvabase
    eqcomd
    adantr
    @2
    @12
    cU
    cbs
    cfv
    #
    wceq
    @5
    @2
    @15
    @12
    @12
    cU
    cH
    cK
    @15
    cW
    chlt
    dialss.h
    @12
    eqid
    #
    dialss.u
    @15
    eqid
    dvavbase
    eqcomd
    adantr
    @6
    @8
    eqidd
    @6
    @9
    eqidd
    cS
    cU
    clss
    cfv
    wceq
    @6
    dialss.s
    a1i
    cB
    @12
    cH
    cI
    cK
    c.le
    chlt
    cW
    cX
    dialss.b
    dialss.l
    dialss.h
    @16
    dialss.i
    diass
    cB
    cH
    cI
    cK
    c.le
    cW
    cX
    dialss.b
    dialss.l
    dialss.h
    dialss.i
    dian0
    @6
    vx
    cv
    #
    @7
    wcel
    #
    va
    cv
    #
    @10
    wcel
    #
    vb
    cv
    #
    @10
    wcel
    #
    w3a
    #
    wa
    #
    @17
    @19
    @9
    co
    #
    @21
    @8
    co
    #
    @19
    @17
    cfv
    #
    @21
    ccom
    #
    @10
    @24
    @26
    @27
    @21
    @8
    co
    #
    @28
    @24
    @25
    @27
    @21
    @8
    @24
    @2
    @18
    @19
    @12
    wcel
    #
    @25
    @27
    wceq
    @2
    @5
    @23
    simpll
    #
    @6
    @18
    @20
    @22
    simpr1
    #
    @24
    @2
    @5
    @20
    @30
    @31
    @2
    @5
    @23
    simplr
    #
    @6
    @18
    @20
    @22
    simpr2
    #
    cB
    @12
    @19
    cH
    cI
    cK
    c.le
    chlt
    cW
    cX
    dialss.b
    dialss.l
    dialss.h
    @16
    dialss.i
    diael
    syl3anc
    #
    @17
    @12
    @9
    cU
    @7
    @19
    cH
    cK
    chlt
    cW
    dialss.h
    @16
    @14
    dialss.u
    @9
    eqid
    dvavsca
    syl12anc
    oveq1d
    @24
    @2
    @27
    @12
    wcel
    #
    @21
    @12
    wcel
    #
    @29
    @28
    wceq
    @31
    @24
    @2
    @18
    @30
    @36
    @31
    @32
    @35
    @17
    @12
    @7
    @19
    cH
    cK
    chlt
    cW
    dialss.h
    @16
    @14
    tendocl
    syl3anc
    #
    @24
    @2
    @5
    @22
    @37
    @31
    @33
    @6
    @18
    @20
    @22
    simpr3
    #
    cB
    @12
    @21
    cH
    cI
    cK
    c.le
    chlt
    cW
    cX
    dialss.b
    dialss.l
    dialss.h
    @16
    dialss.i
    diael
    syl3anc
    #
    @8
    @12
    cU
    @27
    @21
    cH
    cK
    chlt
    cW
    dialss.h
    @16
    dialss.u
    @8
    eqid
    dvavadd
    syl12anc
    eqtrd
    @24
    @28
    @10
    wcel
    #
    @28
    @12
    wcel
    #
    @28
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cfv
    #
    cX
    c.le
    wbr
    #
    @24
    @2
    @36
    @37
    @42
    @31
    @38
    @40
    @12
    @27
    @21
    cH
    cK
    cW
    dialss.h
    @16
    ltrnco
    syl3anc
    #
    @24
    cB
    cK
    c.le
    @44
    @27
    @43
    cfv
    #
    @21
    @43
    cfv
    #
    cK
    cjn
    cfv
    #
    co
    #
    cX
    dialss.b
    dialss.l
    @0
    cK
    clat
    wcel
    #
    @1
    @5
    @23
    cK
    hllat
    ad3antrrr
    #
    @24
    @2
    @42
    @44
    cB
    wcel
    @31
    @46
    cB
    @43
    @12
    @28
    cH
    cK
    cW
    dialss.b
    dialss.h
    @16
    @43
    eqid
    #
    trlcl
    syl2anc
    @24
    @51
    @47
    cB
    wcel
    #
    @48
    cB
    wcel
    #
    @50
    cB
    wcel
    @52
    @24
    @2
    @36
    @54
    @31
    @38
    cB
    @43
    @12
    @27
    cH
    cK
    cW
    dialss.b
    dialss.h
    @16
    @53
    trlcl
    syl2anc
    #
    @24
    @2
    @37
    @55
    @31
    @40
    cB
    @43
    @12
    @21
    cH
    cK
    cW
    dialss.b
    dialss.h
    @16
    @53
    trlcl
    syl2anc
    #
    cB
    @49
    cK
    @47
    @48
    dialss.b
    @49
    eqid
    #
    latjcl
    syl3anc
    @2
    @3
    @4
    @23
    simplrl
    #
    @24
    @2
    @36
    @37
    @44
    @50
    c.le
    wbr
    @31
    @38
    @40
    @43
    @12
    @27
    @21
    cH
    @49
    cK
    c.le
    cW
    dialss.l
    @58
    dialss.h
    @16
    @53
    trlco
    syl3anc
    @24
    @47
    cX
    c.le
    wbr
    #
    @48
    cX
    c.le
    wbr
    #
    @50
    cX
    c.le
    wbr
    #
    @24
    cB
    cK
    c.le
    @47
    @19
    @43
    cfv
    #
    cX
    dialss.b
    dialss.l
    @52
    @56
    @24
    @2
    @30
    @63
    cB
    wcel
    @31
    @35
    cB
    @43
    @12
    @19
    cH
    cK
    cW
    dialss.b
    dialss.h
    @16
    @53
    trlcl
    syl2anc
    @59
    @24
    @2
    @18
    @30
    @47
    @63
    c.le
    wbr
    @31
    @32
    @35
    @43
    @17
    @12
    @7
    @19
    cH
    cK
    c.le
    chlt
    cW
    dialss.l
    dialss.h
    @16
    @53
    @14
    tendotp
    syl3anc
    @24
    @2
    @5
    @20
    @63
    cX
    c.le
    wbr
    @31
    @33
    @34
    cB
    @43
    @12
    @19
    cH
    cI
    cK
    c.le
    chlt
    cW
    cX
    dialss.b
    dialss.l
    dialss.h
    @16
    @53
    dialss.i
    diatrl
    syl3anc
    lattrd
    @24
    @2
    @5
    @22
    @61
    @31
    @33
    @39
    cB
    @43
    @12
    @21
    cH
    cI
    cK
    c.le
    chlt
    cW
    cX
    dialss.b
    dialss.l
    dialss.h
    @16
    @53
    dialss.i
    diatrl
    syl3anc
    @24
    @51
    @54
    @55
    @3
    @60
    @61
    wa
    @62
    wb
    @52
    @56
    @57
    @59
    cB
    @49
    cK
    c.le
    @47
    @48
    cX
    dialss.b
    dialss.l
    @58
    latjle12
    syl13anc
    mpbi2and
    lattrd
    @6
    @41
    @42
    @45
    wa
    wb
    @23
    cB
    @43
    @12
    @28
    cH
    cI
    cK
    c.le
    chlt
    cW
    cX
    dialss.b
    dialss.l
    dialss.h
    @16
    @53
    dialss.i
    diaelval
    adantr
    mpbir2and
    eqeltrd
    islssd
end
