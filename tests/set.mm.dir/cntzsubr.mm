include "crg.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "csubrg.mm"
include "csubg.mm"
include "csubmnd.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "cminusg.mm"
include "mgpbas.mm"
include "cntzssv.mm"
include "a1i.mm"
include "c0g.mm"
include "cmulr.mm"
include "wceq.mm"
include "simpll.mm"
include "ssel2.mm"
include "adantll.mm"
include "eqid.mm"
include "ringlz.mm"
include "syl2anc.mm"
include "ringrz.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "wb.mm"
include "simpr.mm"
include "ring0cl.mm"
include "adantr.mm"
include "mgpplusg.mm"
include "cntzel.mm"
include "mpbird.mm"
include "ne0i.mm"
include "syl.mm"
include "w3a.mm"
include "simpl2.mm"
include "cntzi.mm"
include "simpl3.mm"
include "oveq12d.mm"
include "simpl1l.mm"
include "sseldi.mm"
include "simp1r.mm"
include "sselda.mm"
include "ringdir.mm"
include "syl13anc.mm"
include "ringdi.mm"
include "3eqtr4d.mm"
include "simp1l.mm"
include "simp2.mm"
include "simp3.mm"
include "ringacl.mm"
include "syl3anc.mm"
include "3expa.mm"
include "fveq2d.mm"
include "simplll.mm"
include "simplr.mm"
include "ringmneg1.mm"
include "ringmneg2.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "ad2antrr.mm"
include "grpinvcl.mm"
include "jca.mm"
include "issubg2.mm"
include "mpbir3and.mm"
include "cmnd.mm"
include "ringmgp.mm"
include "cntzsubm.mm"
include "sylan.mm"
include "issubrg3.mm"
include "mpbir2and.mm"

theorem cntzsubr
  let cB: class B
  let cR: class R
  let cS: class S
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cntzsubr.b: |- B = ( Base ` R )
  assume cntzsubr.m: |- M = ( mulGrp ` R )
  assume cntzsubr.z: |- Z = ( Cntz ` M )


  assert |- ( ( R e. Ring /\ S C_ B ) -> ( Z ` S ) e. ( SubRing ` R ) )

  proof
    cR
    crg
    wcel
    #
    cS
    cB
    wss
    #
    wa
    #
    cS
    cZ
    cfv
    #
    cR
    csubrg
    cfv
    wcel
    #
    @3
    cR
    csubg
    cfv
    wcel
    #
    @3
    cM
    csubmnd
    cfv
    wcel
    #
    @2
    @5
    @3
    cB
    wss
    #
    @3
    c0
    wne
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    cplusg
    cfv
    #
    co
    #
    @3
    wcel
    #
    vy
    @3
    wral
    #
    @9
    cR
    cminusg
    cfv
    #
    cfv
    #
    @3
    wcel
    #
    wa
    #
    vx
    @3
    wral
    #
    @7
    @2
    cB
    cS
    cM
    cZ
    cB
    cR
    cM
    cntzsubr.m
    cntzsubr.b
    mgpbas
    #
    cntzsubr.z
    cntzssv
    #
    a1i
    @2
    cR
    c0g
    cfv
    #
    @3
    wcel
    #
    @8
    @2
    @23
    @22
    vz
    cv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    @24
    @22
    @25
    co
    #
    wceq
    #
    vz
    cS
    wral
    #
    @2
    @28
    vz
    cS
    @2
    @24
    cS
    wcel
    #
    wa
    #
    @26
    @22
    @27
    @31
    @0
    @24
    cB
    wcel
    #
    @26
    @22
    wceq
    @0
    @1
    @30
    simpll
    #
    @1
    @30
    @32
    @0
    cS
    cB
    @24
    ssel2
    adantll
    #
    cB
    cR
    @25
    @24
    @22
    cntzsubr.b
    @25
    eqid
    #
    @22
    eqid
    #
    ringlz
    syl2anc
    @31
    @0
    @32
    @27
    @22
    wceq
    @33
    @34
    cB
    cR
    @25
    @24
    @22
    cntzsubr.b
    @35
    @36
    ringrz
    syl2anc
    eqtr4d
    ralrimiva
    @2
    @1
    @22
    cB
    wcel
    #
    @23
    @29
    wb
    @0
    @1
    simpr
    @0
    @37
    @1
    cB
    cR
    @22
    cntzsubr.b
    @36
    ring0cl
    adantr
    vz
    cB
    @25
    cS
    cM
    @22
    cZ
    @20
    cR
    @25
    cM
    cntzsubr.m
    @35
    mgpplusg
    #
    cntzsubr.z
    cntzel
    syl2anc
    mpbird
    @3
    @22
    ne0i
    syl
    @2
    @18
    vx
    @3
    @2
    @9
    @3
    wcel
    #
    wa
    #
    @14
    @17
    @40
    @13
    vy
    @3
    @2
    @39
    @10
    @3
    wcel
    #
    @13
    @2
    @39
    @41
    w3a
    #
    @13
    @12
    @24
    @25
    co
    #
    @24
    @12
    @25
    co
    #
    wceq
    #
    vz
    cS
    wral
    #
    @42
    @45
    vz
    cS
    @42
    @30
    wa
    #
    @9
    @24
    @25
    co
    #
    @10
    @24
    @25
    co
    #
    @11
    co
    #
    @24
    @9
    @25
    co
    #
    @24
    @10
    @25
    co
    #
    @11
    co
    #
    @43
    @44
    @47
    @48
    @51
    @49
    @52
    @11
    @47
    @39
    @30
    @48
    @51
    wceq
    #
    @2
    @39
    @41
    @30
    simpl2
    #
    @42
    @30
    simpr
    #
    @25
    cS
    cM
    @9
    @24
    cZ
    @38
    cntzsubr.z
    cntzi
    #
    syl2anc
    @47
    @41
    @30
    @49
    @52
    wceq
    @2
    @39
    @41
    @30
    simpl3
    #
    @56
    @25
    cS
    cM
    @10
    @24
    cZ
    @38
    cntzsubr.z
    cntzi
    syl2anc
    oveq12d
    @47
    @0
    @9
    cB
    wcel
    #
    @10
    cB
    wcel
    #
    @32
    @43
    @50
    wceq
    @0
    @1
    @39
    @41
    @30
    simpl1l
    #
    @47
    @3
    cB
    @9
    @21
    @55
    sseldi
    #
    @47
    @3
    cB
    @10
    @21
    @58
    sseldi
    #
    @42
    cS
    cB
    @24
    @0
    @1
    @39
    @41
    simp1r
    #
    sselda
    #
    cB
    @11
    cR
    @25
    @9
    @10
    @24
    cntzsubr.b
    @11
    eqid
    #
    @35
    ringdir
    syl13anc
    @47
    @0
    @32
    @59
    @60
    @44
    @53
    wceq
    @61
    @65
    @62
    @63
    cB
    @11
    cR
    @25
    @24
    @9
    @10
    cntzsubr.b
    @66
    @35
    ringdi
    syl13anc
    3eqtr4d
    ralrimiva
    @42
    @1
    @12
    cB
    wcel
    #
    @13
    @46
    wb
    @64
    @42
    @0
    @59
    @60
    @67
    @0
    @1
    @39
    @41
    simp1l
    @42
    @3
    cB
    @9
    @21
    @2
    @39
    @41
    simp2
    sseldi
    @42
    @3
    cB
    @10
    @21
    @2
    @39
    @41
    simp3
    sseldi
    cB
    @11
    cR
    @9
    @10
    cntzsubr.b
    @66
    ringacl
    syl3anc
    vz
    cB
    @25
    cS
    cM
    @12
    cZ
    @20
    @38
    cntzsubr.z
    cntzel
    syl2anc
    mpbird
    3expa
    ralrimiva
    @40
    @17
    @16
    @24
    @25
    co
    #
    @24
    @16
    @25
    co
    #
    wceq
    #
    vz
    cS
    wral
    #
    @40
    @70
    vz
    cS
    @40
    @30
    wa
    #
    @48
    @15
    cfv
    @51
    @15
    cfv
    @68
    @69
    @72
    @48
    @51
    @15
    @39
    @30
    @54
    @2
    @57
    adantll
    fveq2d
    @72
    cB
    cR
    @25
    @15
    @9
    @24
    cntzsubr.b
    @35
    @15
    eqid
    #
    @0
    @1
    @39
    @30
    simplll
    #
    @72
    @3
    cB
    @9
    @21
    @2
    @39
    @30
    simplr
    sseldi
    #
    @40
    cS
    cB
    @24
    @0
    @1
    @39
    simplr
    #
    sselda
    #
    ringmneg1
    @72
    cB
    cR
    @25
    @15
    @24
    @9
    cntzsubr.b
    @35
    @73
    @74
    @77
    @75
    ringmneg2
    3eqtr4d
    ralrimiva
    @40
    @1
    @16
    cB
    wcel
    #
    @17
    @71
    wb
    @76
    @40
    cR
    cgrp
    wcel
    #
    @59
    @78
    @0
    @79
    @1
    @39
    cR
    ringgrp
    #
    ad2antrr
    @40
    @3
    cB
    @9
    @21
    @2
    @39
    simpr
    sseldi
    cB
    cR
    @15
    @9
    cntzsubr.b
    @73
    grpinvcl
    syl2anc
    vz
    cB
    @25
    cS
    cM
    @16
    cZ
    @20
    @38
    cntzsubr.z
    cntzel
    syl2anc
    mpbird
    jca
    ralrimiva
    @2
    @79
    @5
    @7
    @8
    @19
    w3a
    wb
    @0
    @79
    @1
    @80
    adantr
    vx
    vy
    cB
    @11
    @3
    cR
    @15
    cntzsubr.b
    @66
    @73
    issubg2
    syl
    mpbir3and
    @0
    cM
    cmnd
    wcel
    @1
    @6
    cR
    cM
    cntzsubr.m
    ringmgp
    cB
    cS
    cM
    cZ
    @20
    cntzsubr.z
    cntzsubm
    sylan
    @0
    @4
    @5
    @6
    wa
    wb
    @1
    cR
    @3
    cM
    cntzsubr.m
    issubrg3
    adantr
    mpbir2and
end
