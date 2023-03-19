include "cdr.mm"
include "wcel.mm"
include "crg.mm"
include "cui.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "wceq.mm"
include "wa.mm"
include "cgrp.mm"
include "eqid.mm"
include "isdrng.mm"
include "cmgp.mm"
include "cress.mm"
include "co.mm"
include "oveq2.mm"
include "adantl.mm"
include "syl6eqr.mm"
include "unitgrp.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "cv.mm"
include "wne.mm"
include "unitcl.mm"
include "c0g.mm"
include "cdvr.mm"
include "cmulr.mm"
include "wss.mm"
include "cbs.mm"
include "difss.mm"
include "mgpbas.mm"
include "ressbas2.mm"
include "ax-mp.mm"
include "grpidcl.mm"
include "ad2antlr.mm"
include "eldifsn.mm"
include "sylib.mm"
include "simprd.mm"
include "simpll.mm"
include "eldifad.mm"
include "simpr.mm"
include "dvrcan1.mm"
include "syl3anc.mm"
include "dvrcl.mm"
include "ringrz.mm"
include "syl2anc.mm"
include "3netr4d.mm"
include "necon3i.mm"
include "syl.mm"
include "sylanbrc.mm"
include "ex.mm"
include "ssrdv.mm"
include "cur.mm"
include "cdsr.mm"
include "wbr.mm"
include "coppr.mm"
include "cminusg.mm"
include "eldifi.mm"
include "grpinvcl.mm"
include "adantll.mm"
include "dvdsrmul.mm"
include "cvv.mm"
include "cplusg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "difexg.mm"
include "mgpplusg.mm"
include "ressplusg.mm"
include "mp2b.mm"
include "grplinv.mm"
include "ringidcl.mm"
include "ringlidm.mm"
include "mpdan.mm"
include "wb.mm"
include "1unit.mm"
include "sseldd.mm"
include "grpid.mm"
include "mpbid.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "opprbas.mm"
include "opprmul.mm"
include "grprinv.mm"
include "syl5eq.mm"
include "isunit.mm"
include "eqssd.mm"
include "impbida.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem isdrng2
  let cB: class B
  let cR: class R
  let cG: class G
  let c.0: class .0.
  let vx: setvar x
  assume isdrng2.b: |- B = ( Base ` R )
  assume isdrng2.z: |- .0. = ( 0g ` R )
  assume isdrng2.g: |- G = ( ( mulGrp ` R ) |`s ( B \ { .0. } ) )


  assert |- ( R e. DivRing <-> ( R e. Ring /\ G e. Grp ) )

  proof
    cR
    cdr
    wcel
    cR
    crg
    wcel
    #
    cR
    cui
    cfv
    #
    cB
    c.0
    csn
    #
    cdif
    #
    wceq
    #
    wa
    #
    @0
    cG
    cgrp
    wcel
    #
    wa
    #
    cB
    cR
    @1
    c.0
    isdrng2.b
    @1
    eqid
    #
    isdrng2.z
    isdrng
    @0
    @4
    @6
    @0
    @4
    @6
    @5
    cR
    cmgp
    cfv
    #
    @1
    cress
    co
    #
    cG
    cgrp
    @5
    @10
    @9
    @3
    cress
    co
    #
    cG
    @4
    @10
    @11
    wceq
    @0
    @1
    @3
    @9
    cress
    oveq2
    adantl
    isdrng2.g
    syl6eqr
    @0
    @10
    cgrp
    wcel
    @4
    cR
    @1
    @10
    @8
    @10
    eqid
    unitgrp
    adantr
    eqeltrrd
    @7
    @1
    @3
    @7
    vx
    @1
    @3
    @7
    vx
    cv
    #
    @1
    wcel
    #
    @12
    @3
    wcel
    #
    @7
    @13
    wa
    #
    @12
    cB
    wcel
    #
    @12
    c.0
    wne
    #
    @14
    @13
    @16
    @7
    cB
    cR
    @1
    @12
    isdrng2.b
    @8
    unitcl
    adantl
    @15
    cG
    c0g
    cfv
    #
    @12
    cR
    cdvr
    cfv
    #
    co
    #
    @12
    cR
    cmulr
    cfv
    #
    co
    #
    @20
    c.0
    @21
    co
    #
    wne
    @17
    @15
    @18
    c.0
    @22
    @23
    @15
    @18
    cB
    wcel
    #
    @18
    c.0
    wne
    #
    @15
    @18
    @3
    wcel
    #
    @24
    @25
    wa
    @6
    @26
    @0
    @13
    @3
    cG
    @18
    @3
    cB
    wss
    @3
    cG
    cbs
    cfv
    wceq
    cB
    @2
    difss
    @3
    cB
    cG
    @9
    isdrng2.g
    cB
    cR
    @9
    @9
    eqid
    #
    isdrng2.b
    mgpbas
    ressbas2
    ax-mp
    #
    @18
    eqid
    #
    grpidcl
    ad2antlr
    #
    @18
    cB
    c.0
    eldifsn
    sylib
    simprd
    @15
    @0
    @24
    @13
    @22
    @18
    wceq
    @0
    @6
    @13
    simpll
    #
    @15
    @18
    cB
    @2
    @30
    eldifad
    #
    @7
    @13
    simpr
    #
    cB
    @19
    cR
    @21
    @1
    @18
    @12
    isdrng2.b
    @8
    @19
    eqid
    #
    @21
    eqid
    #
    dvrcan1
    syl3anc
    @15
    @0
    @20
    cB
    wcel
    #
    @23
    c.0
    wceq
    @31
    @15
    @0
    @24
    @13
    @36
    @31
    @32
    @33
    cB
    @19
    cR
    @1
    @18
    @12
    isdrng2.b
    @8
    @34
    dvrcl
    syl3anc
    cB
    cR
    @21
    @20
    c.0
    isdrng2.b
    @35
    isdrng2.z
    ringrz
    syl2anc
    3netr4d
    @12
    c.0
    @22
    @23
    @12
    c.0
    @20
    @21
    oveq2
    necon3i
    syl
    @12
    cB
    c.0
    eldifsn
    sylanbrc
    ex
    ssrdv
    #
    @7
    vx
    @3
    @1
    @7
    @14
    @13
    @7
    @14
    wa
    #
    @12
    cR
    cur
    cfv
    #
    cR
    cdsr
    cfv
    #
    wbr
    @12
    @39
    cR
    coppr
    cfv
    #
    cdsr
    cfv
    #
    wbr
    @13
    @38
    @12
    @12
    cG
    cminusg
    cfv
    #
    cfv
    #
    @12
    @21
    co
    #
    @39
    @40
    @38
    @16
    @44
    cB
    wcel
    #
    @12
    @45
    @40
    wbr
    @14
    @16
    @7
    @12
    cB
    @2
    eldifi
    adantl
    #
    @38
    @44
    cB
    @2
    @6
    @14
    @44
    @3
    wcel
    @0
    @3
    cG
    @43
    @12
    @28
    @43
    eqid
    #
    grpinvcl
    adantll
    eldifad
    #
    cB
    @40
    cR
    @21
    @12
    @44
    isdrng2.b
    @40
    eqid
    #
    @35
    dvdsrmul
    syl2anc
    @38
    @45
    @18
    @39
    @6
    @14
    @45
    @18
    wceq
    @0
    @3
    @21
    cG
    @43
    @12
    @18
    @28
    cB
    cvv
    wcel
    @3
    cvv
    wcel
    @21
    cG
    cplusg
    cfv
    wceq
    cB
    cR
    cbs
    cfv
    cvv
    isdrng2.b
    cR
    cbs
    fvex
    eqeltri
    cB
    @2
    cvv
    difexg
    @3
    @21
    @9
    cG
    cvv
    isdrng2.g
    cR
    @21
    @9
    @27
    @35
    mgpplusg
    ressplusg
    mp2b
    #
    @29
    @48
    grplinv
    adantll
    @7
    @18
    @39
    wceq
    #
    @14
    @7
    @39
    @39
    @21
    co
    @39
    wceq
    #
    @52
    @0
    @53
    @6
    @0
    @39
    cB
    wcel
    @53
    cB
    cR
    @39
    isdrng2.b
    @39
    eqid
    #
    ringidcl
    cB
    cR
    @21
    @39
    @39
    isdrng2.b
    @35
    @54
    ringlidm
    mpdan
    adantr
    @7
    @6
    @39
    @3
    wcel
    @53
    @52
    wb
    @0
    @6
    simpr
    @7
    @1
    @3
    @39
    @37
    @0
    @39
    @1
    wcel
    @6
    cR
    @1
    @39
    @8
    @54
    1unit
    adantr
    sseldd
    @3
    @21
    cG
    @39
    @18
    @28
    @51
    @29
    grpid
    syl2anc
    mpbid
    adantr
    #
    eqtrd
    breqtrd
    @38
    @12
    @44
    @12
    @41
    cmulr
    cfv
    #
    co
    #
    @39
    @42
    @38
    @16
    @46
    @12
    @57
    @42
    wbr
    @47
    @49
    cB
    @42
    @41
    @56
    @12
    @44
    cB
    cR
    @41
    @41
    eqid
    #
    isdrng2.b
    opprbas
    @42
    eqid
    #
    @56
    eqid
    #
    dvdsrmul
    syl2anc
    @38
    @57
    @12
    @44
    @21
    co
    #
    @39
    cB
    cR
    @56
    @21
    @41
    @44
    @12
    isdrng2.b
    @35
    @58
    @60
    opprmul
    @38
    @61
    @18
    @39
    @6
    @14
    @61
    @18
    wceq
    @0
    @3
    @21
    cG
    @43
    @12
    @18
    @28
    @51
    @29
    @48
    grprinv
    adantll
    @55
    eqtrd
    syl5eq
    breqtrd
    @40
    cR
    @41
    @1
    @39
    @42
    @12
    @8
    @54
    @50
    @58
    @59
    isunit
    sylanbrc
    ex
    ssrdv
    eqssd
    impbida
    pm5.32i
    bitri
end
