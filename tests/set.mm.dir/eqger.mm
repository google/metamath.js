include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wrel.mm"
include "releqg.mm"
include "a1i.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "cminusg.mm"
include "cplusg.mm"
include "co.mm"
include "w3a.mm"
include "cgrp.mm"
include "wss.mm"
include "wb.mm"
include "subgrcl.mm"
include "subgss.mm"
include "eqid.mm"
include "eqgval.mm"
include "syl2anc.mm"
include "biimpa.mm"
include "simp2d.mm"
include "simp1d.mm"
include "wceq.mm"
include "adantr.mm"
include "grpinvcl.mm"
include "grpinvadd.mm"
include "syl3anc.mm"
include "grpinvinv.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "simp3d.mm"
include "subginvcl.mm"
include "syldan.mm"
include "eqeltrrd.mm"
include "mpbir3and.mm"
include "adantrr.mm"
include "adantrl.mm"
include "grpcl.mm"
include "grpass.mm"
include "syl13anc.mm"
include "c0g.mm"
include "grprinv.mm"
include "oveq1d.mm"
include "grplid.mm"
include "3eqtr3d.mm"
include "simpl.mm"
include "subgcl.mm"
include "grplinv.mm"
include "sylan.mm"
include "subg0cl.mm"
include "eqeltrd.mm"
include "ex.mm"
include "pm4.71rd.mm"
include "df-3an.mm"
include "anidm.mm"
include "anbi2ci.mm"
include "bitri.mm"
include "syl6bb.mm"
include "bitr4d.mm"
include "iserd.mm"

theorem eqger
  let c.sm: class .~
  let cG: class G
  let cX: class X
  let cY: class Y
  let vg: setvar g
  let vx: setvar x
  let c.pl: class .+
  let vy: setvar y
  let vz: setvar z
  let c.0: class .0.
  let cA: class A
  assume eqger.x: |- X = ( Base ` G )
  assume eqger.r: |- .~ = ( G ~QG Y )


  assert |- ( Y e. ( SubGrp ` G ) -> .~ Er X )

  proof
    cY
    cG
    csubg
    cfv
    wcel
    #
    vx
    vy
    vz
    cX
    c.sm
    c.sm
    wrel
    @0
    c.sm
    cY
    cG
    eqger.r
    releqg
    a1i
    @0
    vx
    cv
    #
    vy
    cv
    #
    c.sm
    wbr
    #
    wa
    #
    @2
    @1
    c.sm
    wbr
    #
    @2
    cX
    wcel
    #
    @1
    cX
    wcel
    #
    @2
    cG
    cminusg
    cfv
    #
    cfv
    #
    @1
    cG
    cplusg
    cfv
    #
    co
    #
    cY
    wcel
    #
    @4
    @7
    @6
    @1
    @8
    cfv
    #
    @2
    @10
    co
    #
    cY
    wcel
    #
    @0
    @3
    @7
    @6
    @15
    w3a
    #
    @0
    cG
    cgrp
    wcel
    #
    cY
    cX
    wss
    #
    @3
    @16
    wb
    cY
    cG
    subgrcl
    #
    cX
    cY
    cG
    eqger.x
    subgss
    #
    @1
    @2
    @10
    c.sm
    cY
    cG
    @8
    cgrp
    cX
    eqger.x
    @8
    eqid
    #
    @10
    eqid
    #
    eqger.r
    eqgval
    syl2anc
    biimpa
    #
    simp2d
    #
    @4
    @7
    @6
    @15
    @23
    simp1d
    #
    @4
    @14
    @8
    cfv
    #
    @11
    cY
    @4
    @26
    @9
    @13
    @8
    cfv
    #
    @10
    co
    #
    @11
    @4
    @17
    @13
    cX
    wcel
    #
    @6
    @26
    @28
    wceq
    @0
    @17
    @3
    @19
    adantr
    #
    @4
    @17
    @7
    @29
    @30
    @25
    cX
    cG
    @8
    @1
    eqger.x
    @21
    grpinvcl
    #
    syl2anc
    @24
    cX
    @10
    cG
    @8
    @13
    @2
    eqger.x
    @22
    @21
    grpinvadd
    syl3anc
    @4
    @27
    @1
    @9
    @10
    @4
    @17
    @7
    @27
    @1
    wceq
    @30
    @25
    cX
    cG
    @8
    @1
    eqger.x
    @21
    grpinvinv
    syl2anc
    oveq2d
    eqtrd
    @0
    @3
    @15
    @26
    cY
    wcel
    @4
    @7
    @6
    @15
    @23
    simp3d
    #
    cY
    cG
    @8
    @14
    @21
    subginvcl
    syldan
    eqeltrrd
    @4
    @17
    @18
    @5
    @6
    @7
    @12
    w3a
    wb
    @30
    @0
    @18
    @3
    @20
    adantr
    @2
    @1
    @10
    c.sm
    cY
    cG
    @8
    cgrp
    cX
    eqger.x
    @21
    @22
    eqger.r
    eqgval
    syl2anc
    mpbir3and
    @0
    @3
    @2
    vz
    cv
    #
    c.sm
    wbr
    #
    wa
    #
    wa
    #
    @1
    @33
    c.sm
    wbr
    #
    @7
    @33
    cX
    wcel
    #
    @13
    @33
    @10
    co
    #
    cY
    wcel
    #
    @0
    @3
    @7
    @34
    @25
    adantrr
    #
    @36
    @6
    @38
    @9
    @33
    @10
    co
    #
    cY
    wcel
    #
    @0
    @34
    @6
    @38
    @43
    w3a
    #
    @3
    @0
    @34
    @44
    @0
    @17
    @18
    @34
    @44
    wb
    @19
    @20
    @2
    @33
    @10
    c.sm
    cY
    cG
    @8
    cgrp
    cX
    eqger.x
    @21
    @22
    eqger.r
    eqgval
    syl2anc
    biimpa
    adantrl
    #
    simp2d
    #
    @36
    @14
    @42
    @10
    co
    #
    @39
    cY
    @36
    @47
    @13
    @2
    @42
    @10
    co
    #
    @10
    co
    #
    @39
    @36
    @17
    @29
    @6
    @42
    cX
    wcel
    #
    @47
    @49
    wceq
    @0
    @17
    @35
    @19
    adantr
    #
    @36
    @17
    @7
    @29
    @51
    @41
    @31
    syl2anc
    @0
    @3
    @6
    @34
    @24
    adantrr
    #
    @36
    @17
    @9
    cX
    wcel
    #
    @38
    @50
    @51
    @36
    @17
    @6
    @53
    @51
    @52
    cX
    cG
    @8
    @2
    eqger.x
    @21
    grpinvcl
    syl2anc
    #
    @46
    cX
    @10
    cG
    @9
    @33
    eqger.x
    @22
    grpcl
    syl3anc
    cX
    @10
    cG
    @13
    @2
    @42
    eqger.x
    @22
    grpass
    syl13anc
    @36
    @48
    @33
    @13
    @10
    @36
    @2
    @9
    @10
    co
    #
    @33
    @10
    co
    #
    cG
    c0g
    cfv
    #
    @33
    @10
    co
    #
    @48
    @33
    @36
    @55
    @57
    @33
    @10
    @36
    @17
    @6
    @55
    @57
    wceq
    @51
    @52
    cX
    @10
    cG
    @8
    @2
    @57
    eqger.x
    @22
    @57
    eqid
    #
    @21
    grprinv
    syl2anc
    oveq1d
    @36
    @17
    @6
    @53
    @38
    @56
    @48
    wceq
    @51
    @52
    @54
    @46
    cX
    @10
    cG
    @2
    @9
    @33
    eqger.x
    @22
    grpass
    syl13anc
    @36
    @17
    @38
    @58
    @33
    wceq
    @51
    @46
    cX
    @10
    cG
    @33
    @57
    eqger.x
    @22
    @59
    grplid
    syl2anc
    3eqtr3d
    oveq2d
    eqtrd
    @36
    @0
    @15
    @43
    @47
    cY
    wcel
    @0
    @35
    simpl
    @0
    @3
    @15
    @34
    @32
    adantrr
    @36
    @6
    @38
    @43
    @45
    simp3d
    @10
    cY
    cG
    @14
    @42
    @22
    subgcl
    syl3anc
    eqeltrrd
    @36
    @17
    @18
    @37
    @7
    @38
    @40
    w3a
    wb
    @51
    @0
    @18
    @35
    @20
    adantr
    @1
    @33
    @10
    c.sm
    cY
    cG
    @8
    cgrp
    cX
    eqger.x
    @21
    @22
    eqger.r
    eqgval
    syl2anc
    mpbir3and
    @0
    @7
    @13
    @1
    @10
    co
    #
    cY
    wcel
    #
    @7
    wa
    #
    @1
    @1
    c.sm
    wbr
    #
    @0
    @7
    @61
    @0
    @7
    @61
    @0
    @7
    wa
    @60
    @57
    cY
    @0
    @17
    @7
    @60
    @57
    wceq
    @19
    cX
    @10
    cG
    @8
    @1
    @57
    eqger.x
    @22
    @59
    @21
    grplinv
    sylan
    @0
    @57
    cY
    wcel
    @7
    cY
    cG
    @57
    @59
    subg0cl
    adantr
    eqeltrd
    ex
    pm4.71rd
    @0
    @63
    @7
    @7
    @61
    w3a
    #
    @62
    @0
    @17
    @18
    @63
    @64
    wb
    @19
    @20
    @1
    @1
    @10
    c.sm
    cY
    cG
    @8
    cgrp
    cX
    eqger.x
    @21
    @22
    eqger.r
    eqgval
    syl2anc
    @64
    @7
    @7
    wa
    #
    @61
    wa
    @62
    @7
    @7
    @61
    df-3an
    @65
    @7
    @61
    @7
    anidm
    anbi2ci
    bitri
    syl6bb
    bitr4d
    iserd
end
