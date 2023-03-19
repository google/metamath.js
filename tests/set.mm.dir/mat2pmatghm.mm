include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cplusg.mm"
include "cfv.mm"
include "eqid.mm"
include "matgrp.mm"
include "cgrp.mm"
include "pmatring.mm"
include "ringgrp.mm"
include "syl.mm"
include "mat2pmatf.mm"
include "cv.mm"
include "co.mm"
include "cascl.mm"
include "cmpt2.mm"
include "cof.mm"
include "wceq.mm"
include "cbs.mm"
include "simpl.mm"
include "adantr.mm"
include "ply1ring.mm"
include "ad2antlr.mm"
include "w3a.mm"
include "simp1lr.mm"
include "simp2.mm"
include "simp3.mm"
include "simp1rl.mm"
include "matecld.mm"
include "ply1sclcl.mm"
include "syl2anc.mm"
include "matbas2d.mm"
include "simp1rr.mm"
include "matplusg2.mm"
include "cvv.mm"
include "fvexd.mm"
include "eqidd.mm"
include "offval22.mm"
include "csca.mm"
include "simpr.mm"
include "3ad2ant1.mm"
include "3simpc.mm"
include "matplusgcell.mm"
include "ply1sca.mm"
include "adantl.mm"
include "fveq2d.mm"
include "oveqd.mm"
include "eqtrd.mm"
include "cghm.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "asclghm.mm"
include "wb.mm"
include "eqcomd.mm"
include "eleq2d.mm"
include "mpbird.mm"
include "ghmlin.mm"
include "syl3anc.mm"
include "eqtr2d.mm"
include "mpt2eq3dva.mm"
include "cmnd.mm"
include "matring.mm"
include "ringmnd.mm"
include "anim1i.mm"
include "3anass.mm"
include "sylibr.mm"
include "mndcl.mm"
include "df-3an.mm"
include "sylanbrc.mm"
include "mat2pmatval.mm"
include "anim2i.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "isghmd.mm"

theorem mat2pmatghm
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cT: class T
  let cH: class H
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let cM: class M
  let vm: setvar m
  let vi: setvar i
  let vj: setvar j
  assume mat2pmatbas.t: |- T = ( N matToPolyMat R )
  assume mat2pmatbas.a: |- A = ( N Mat R )
  assume mat2pmatbas.b: |- B = ( Base ` A )
  assume mat2pmatbas.p: |- P = ( Poly1 ` R )
  assume mat2pmatbas.c: |- C = ( N Mat P )
  assume mat2pmatbas0.h: |- H = ( Base ` C )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> T e. ( A GrpHom C ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    vx
    vy
    cA
    cplusg
    cfv
    #
    cC
    cplusg
    cfv
    #
    cA
    cC
    cT
    cB
    cH
    mat2pmatbas.b
    mat2pmatbas0.h
    @3
    eqid
    #
    @4
    eqid
    #
    cA
    cR
    cN
    mat2pmatbas.a
    matgrp
    @2
    cC
    crg
    wcel
    cC
    cgrp
    wcel
    cC
    cP
    cR
    cN
    mat2pmatbas.p
    mat2pmatbas.c
    pmatring
    cC
    ringgrp
    syl
    cA
    cB
    cC
    cP
    cR
    cT
    cH
    cN
    mat2pmatbas.t
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatbas.p
    mat2pmatbas.c
    mat2pmatbas0.h
    mat2pmatf
    @2
    vx
    cv
    #
    cB
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    wa
    #
    vi
    vj
    cN
    cN
    vi
    cv
    #
    vj
    cv
    #
    @7
    @9
    @3
    co
    #
    co
    #
    cP
    cascl
    cfv
    #
    cfv
    #
    cmpt2
    #
    vi
    vj
    cN
    cN
    @13
    @14
    @7
    co
    #
    @17
    cfv
    #
    cmpt2
    #
    vi
    vj
    cN
    cN
    @13
    @14
    @9
    co
    #
    @17
    cfv
    #
    cmpt2
    #
    @4
    co
    #
    @15
    cT
    cfv
    #
    @7
    cT
    cfv
    #
    @9
    cT
    cfv
    #
    @4
    co
    @12
    @26
    @22
    @25
    cP
    cplusg
    cfv
    #
    cof
    co
    #
    @19
    @12
    @22
    cH
    wcel
    @25
    cH
    wcel
    @26
    @31
    wceq
    @12
    vi
    vj
    cC
    cH
    @21
    cP
    cP
    cbs
    cfv
    #
    cN
    crg
    mat2pmatbas.c
    @32
    eqid
    #
    mat2pmatbas0.h
    @2
    @0
    @11
    @0
    @1
    simpl
    adantr
    #
    @1
    cP
    crg
    wcel
    #
    @0
    @11
    cP
    cR
    mat2pmatbas.p
    ply1ring
    ad2antlr
    #
    @12
    @13
    cN
    wcel
    #
    @14
    cN
    wcel
    #
    w3a
    #
    @1
    @20
    cR
    cbs
    cfv
    #
    wcel
    #
    @21
    @32
    wcel
    @0
    @1
    @11
    @37
    @38
    simp1lr
    #
    @39
    cA
    cB
    cR
    @13
    @14
    @40
    @7
    cN
    mat2pmatbas.a
    @40
    eqid
    #
    mat2pmatbas.b
    @12
    @37
    @38
    simp2
    #
    @12
    @37
    @38
    simp3
    #
    @8
    @10
    @2
    @37
    @38
    simp1rl
    matecld
    #
    @17
    @32
    cP
    cR
    @20
    @40
    mat2pmatbas.p
    @17
    eqid
    #
    @43
    @33
    ply1sclcl
    syl2anc
    matbas2d
    @12
    vi
    vj
    cC
    cH
    @24
    cP
    @32
    cN
    crg
    mat2pmatbas.c
    @33
    mat2pmatbas0.h
    @34
    @36
    @39
    @1
    @23
    @40
    wcel
    #
    @24
    @32
    wcel
    @42
    @39
    cA
    cB
    cR
    @13
    @14
    @40
    @9
    cN
    mat2pmatbas.a
    @43
    mat2pmatbas.b
    @44
    @45
    @8
    @10
    @2
    @37
    @38
    simp1rr
    matecld
    #
    @17
    @32
    cP
    cR
    @23
    @40
    mat2pmatbas.p
    @47
    @43
    @33
    ply1sclcl
    syl2anc
    matbas2d
    cC
    cH
    @30
    @4
    cP
    cN
    @22
    @25
    mat2pmatbas.c
    mat2pmatbas0.h
    @6
    @30
    eqid
    #
    matplusg2
    syl2anc
    @12
    @31
    vi
    vj
    cN
    cN
    @21
    @24
    @30
    co
    #
    cmpt2
    @19
    @12
    vi
    vj
    cN
    cN
    @21
    @24
    @30
    @22
    @25
    cfn
    cfn
    cvv
    cvv
    @34
    @34
    @39
    @20
    @17
    fvexd
    @39
    @23
    @17
    fvexd
    @12
    @22
    eqidd
    @12
    @25
    eqidd
    offval22
    @12
    vi
    vj
    cN
    cN
    @51
    @18
    @39
    @18
    @20
    @23
    cP
    csca
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    @17
    cfv
    #
    @51
    @39
    @16
    @54
    @17
    @39
    @16
    @20
    @23
    cR
    cplusg
    cfv
    #
    co
    #
    @54
    @39
    @11
    @37
    @38
    wa
    @16
    @57
    wceq
    @12
    @37
    @11
    @38
    @2
    @11
    simpr
    3ad2ant1
    @12
    @37
    @38
    3simpc
    cA
    cB
    @56
    @3
    cR
    @13
    @14
    cN
    @7
    @9
    mat2pmatbas.a
    mat2pmatbas.b
    @5
    @56
    eqid
    matplusgcell
    syl2anc
    @12
    @37
    @57
    @54
    wceq
    #
    @38
    @2
    @58
    @11
    @2
    @56
    @53
    @20
    @23
    @2
    cR
    @52
    cplusg
    @1
    cR
    @52
    wceq
    @0
    cP
    cR
    crg
    mat2pmatbas.p
    ply1sca
    adantl
    #
    fveq2d
    oveqd
    adantr
    3ad2ant1
    eqtrd
    fveq2d
    @39
    @17
    @52
    cP
    cghm
    co
    wcel
    @20
    @52
    cbs
    cfv
    #
    wcel
    #
    @23
    @60
    wcel
    #
    @55
    @51
    wceq
    @39
    @17
    @52
    cP
    @47
    @52
    eqid
    @12
    @37
    @35
    @38
    @36
    3ad2ant1
    @12
    @37
    cP
    clmod
    wcel
    #
    @38
    @1
    @63
    @0
    @11
    cP
    cR
    mat2pmatbas.p
    ply1lmod
    ad2antlr
    3ad2ant1
    asclghm
    @39
    @61
    @41
    @46
    @12
    @37
    @61
    @41
    wb
    #
    @38
    @2
    @64
    @11
    @2
    @60
    @40
    @20
    @2
    @52
    cR
    cbs
    @2
    cR
    @52
    @59
    eqcomd
    fveq2d
    #
    eleq2d
    adantr
    3ad2ant1
    mpbird
    @39
    @62
    @48
    @49
    @12
    @37
    @62
    @48
    wb
    #
    @38
    @2
    @66
    @11
    @2
    @60
    @40
    @23
    @65
    eleq2d
    adantr
    3ad2ant1
    mpbird
    @53
    @30
    @52
    cP
    @20
    @17
    @23
    @60
    @60
    eqid
    @53
    eqid
    @50
    ghmlin
    syl3anc
    eqtr2d
    mpt2eq3dva
    eqtrd
    eqtr2d
    @12
    @0
    @1
    @15
    cB
    wcel
    #
    w3a
    #
    @27
    @19
    wceq
    @12
    @2
    @67
    @68
    @2
    @11
    simpl
    @12
    cA
    cmnd
    wcel
    #
    @8
    @10
    w3a
    #
    @67
    @12
    @69
    @11
    wa
    @70
    @2
    @69
    @11
    @2
    cA
    crg
    wcel
    @69
    cA
    cR
    cN
    mat2pmatbas.a
    matring
    cA
    ringmnd
    syl
    anim1i
    @69
    @8
    @10
    3anass
    sylibr
    cB
    @3
    cA
    @7
    @9
    mat2pmatbas.b
    @5
    mndcl
    syl
    @0
    @1
    @67
    df-3an
    sylanbrc
    vi
    vj
    cA
    cB
    cP
    cR
    @17
    cT
    @15
    cN
    crg
    mat2pmatbas.t
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatbas.p
    @47
    mat2pmatval
    syl
    @12
    @28
    @22
    @29
    @25
    @4
    @12
    @0
    @1
    @8
    w3a
    #
    @28
    @22
    wceq
    @12
    @2
    @8
    wa
    @71
    @11
    @8
    @2
    @8
    @10
    simpl
    anim2i
    @0
    @1
    @8
    df-3an
    sylibr
    vi
    vj
    cA
    cB
    cP
    cR
    @17
    cT
    @7
    cN
    crg
    mat2pmatbas.t
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatbas.p
    @47
    mat2pmatval
    syl
    @12
    @0
    @1
    @10
    w3a
    #
    @29
    @25
    wceq
    @12
    @2
    @10
    wa
    @72
    @11
    @10
    @2
    @8
    @10
    simpr
    anim2i
    @0
    @1
    @10
    df-3an
    sylibr
    vi
    vj
    cA
    cB
    cP
    cR
    @17
    cT
    @9
    cN
    crg
    mat2pmatbas.t
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatbas.p
    @47
    mat2pmatval
    syl
    oveq12d
    3eqtr4d
    isghmd
end
