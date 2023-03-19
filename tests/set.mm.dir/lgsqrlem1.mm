include "cfv.mm"
include "cur.mm"
include "csg.mm"
include "co.mm"
include "c0g.mm"
include "c1.mm"
include "cmin.mm"
include "c2.mm"
include "cdiv.mm"
include "fveq2i.mm"
include "fveq1i.mm"
include "wcel.mm"
include "wceq.mm"
include "cbs.mm"
include "eqid.mm"
include "cidom.mm"
include "ccrg.mm"
include "cfield.mm"
include "cprime.mm"
include "csn.mm"
include "eldifad.mm"
include "znfld.mm"
include "syl.mm"
include "fldidom.mm"
include "cdomn.mm"
include "isidom.mm"
include "simplbi.mm"
include "cz.mm"
include "zring.mm"
include "crh.mm"
include "wf.mm"
include "crg.mm"
include "crngring.mm"
include "zrhrhm.mm"
include "zringbas.mm"
include "rhmf.mm"
include "ffvelrnd.mm"
include "cmgp.mm"
include "cmg.mm"
include "wa.mm"
include "evl1vard.mm"
include "cdif.mm"
include "cn.mm"
include "oddprm.mm"
include "nnnn0d.mm"
include "evl1expd.mm"
include "ccnfld.mm"
include "cress.mm"
include "cmhm.mm"
include "cn0.mm"
include "zringmpg.mm"
include "rhmmhm.mm"
include "mgpbas.mm"
include "mhmmulg.mm"
include "syl3anc.mm"
include "cexp.mm"
include "csubmnd.mm"
include "csubrg.mm"
include "zsubrg.mm"
include "subrgsubm.mm"
include "mp1i.mm"
include "submmulg.mm"
include "cc.mm"
include "zcnd.mm"
include "cnfldexp.mm"
include "syl2anc.mm"
include "eqtr3d.mm"
include "fveq2d.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmo.mm"
include "wb.mm"
include "prmnn.mm"
include "zexpcl.mm"
include "1zzd.mm"
include "moddvds.mm"
include "mpbid.mm"
include "zndvds.mm"
include "mpbird.mm"
include "zring1.mm"
include "rhm1.mm"
include "3eqtrd.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "cascl.mm"
include "ringidcl.mm"
include "evl1scad.mm"
include "ply1scl1.mm"
include "eleq1d.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "evl1subd.mm"
include "simprd.mm"
include "syl5eq.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "grpsubid.mm"
include "eqtrd.mm"

theorem lgsqrlem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cS: class S
  let cT: class T
  let c.1: class .1.
  let c.ex: class .^
  let cL: class L
  let c.mi: class .-
  let cO: class O
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vz: setvar z
  let cG: class G
  let vy: setvar y
  assume lgsqr.y: |- Y = ( Z/nZ ` P )
  assume lgsqr.s: |- S = ( Poly1 ` Y )
  assume lgsqr.b: |- B = ( Base ` S )
  assume lgsqr.d: |- D = ( deg1 ` Y )
  assume lgsqr.o: |- O = ( eval1 ` Y )
  assume lgsqr.e: |- .^ = ( .g ` ( mulGrp ` S ) )
  assume lgsqr.x: |- X = ( var1 ` Y )
  assume lgsqr.m: |- .- = ( -g ` S )
  assume lgsqr.u: |- .1. = ( 1r ` S )
  assume lgsqr.t: |- T = ( ( ( ( P - 1 ) / 2 ) .^ X ) .- .1. )
  assume lgsqr.l: |- L = ( ZRHom ` Y )
  assume lgsqr.1: |- ( ph -> P e. ( Prime \ { 2 } ) )
  assume lgsqrlem1.3: |- ( ph -> A e. ZZ )
  assume lgsqrlem1.4: |- ( ph -> ( ( A ^ ( ( P - 1 ) / 2 ) ) mod P ) = ( 1 mod P ) )


  assert |- ( ph -> ( ( O ` T ) ` ( L ` A ) ) = ( 0g ` Y ) )

  proof
    wph
    cA
    cL
    cfv
    #
    cT
    cO
    cfv
    #
    cfv
    #
    cY
    cur
    cfv
    #
    @3
    cY
    csg
    cfv
    #
    co
    #
    cY
    c0g
    cfv
    #
    wph
    @2
    @0
    cP
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cX
    c.ex
    co
    #
    c.1
    c.mi
    co
    #
    cO
    cfv
    #
    cfv
    #
    @5
    @0
    @1
    @10
    cT
    @9
    cO
    lgsqr.t
    fveq2i
    fveq1i
    wph
    @9
    cB
    wcel
    @11
    @5
    wceq
    wph
    cY
    cbs
    cfv
    #
    @4
    cS
    cY
    cB
    @8
    c.mi
    c.1
    cO
    @3
    @3
    @0
    lgsqr.o
    lgsqr.s
    @12
    eqid
    #
    lgsqr.b
    wph
    cY
    cidom
    wcel
    #
    cY
    ccrg
    wcel
    #
    wph
    cY
    cfield
    wcel
    #
    @14
    wph
    cP
    cprime
    wcel
    #
    @16
    wph
    cP
    cprime
    c2
    csn
    #
    lgsqr.1
    eldifad
    #
    cP
    cY
    lgsqr.y
    znfld
    syl
    cY
    fldidom
    syl
    @14
    @15
    cY
    cdomn
    wcel
    cY
    isidom
    simplbi
    syl
    #
    wph
    cz
    @12
    cA
    cL
    wph
    cL
    zring
    cY
    crh
    co
    wcel
    #
    cz
    @12
    cL
    wf
    wph
    cY
    crg
    wcel
    #
    @21
    wph
    @15
    @22
    @20
    cY
    crngring
    syl
    #
    cY
    cL
    lgsqr.l
    zrhrhm
    syl
    #
    cz
    @12
    zring
    cY
    cL
    zringbas
    @13
    rhmf
    syl
    lgsqrlem1.3
    ffvelrnd
    #
    wph
    @8
    cB
    wcel
    #
    @0
    @8
    cO
    cfv
    cfv
    #
    @7
    @0
    cY
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    #
    wceq
    #
    wa
    @26
    @27
    @3
    wceq
    #
    wa
    wph
    @12
    cS
    cY
    c.ex
    cB
    @29
    cX
    @7
    cO
    @0
    @0
    lgsqr.o
    lgsqr.s
    @13
    lgsqr.b
    @20
    @25
    wph
    @12
    cS
    cY
    cB
    cO
    cX
    @0
    lgsqr.o
    lgsqr.x
    @13
    lgsqr.s
    lgsqr.b
    @20
    @25
    evl1vard
    lgsqr.e
    @29
    eqid
    #
    wph
    @7
    wph
    cP
    cprime
    @18
    cdif
    wcel
    @7
    cn
    wcel
    lgsqr.1
    cP
    oddprm
    syl
    nnnn0d
    #
    evl1expd
    wph
    @31
    @32
    @26
    wph
    @30
    @3
    @27
    wph
    @7
    cA
    ccnfld
    cmgp
    cfv
    #
    cz
    cress
    co
    #
    cmg
    cfv
    #
    co
    #
    cL
    cfv
    #
    @30
    @3
    wph
    cL
    @36
    @28
    cmhm
    co
    wcel
    #
    @7
    cn0
    wcel
    #
    cA
    cz
    wcel
    #
    @39
    @30
    wceq
    wph
    @21
    @40
    @24
    zring
    cY
    cL
    @36
    @28
    zringmpg
    @28
    eqid
    rhmmhm
    syl
    @34
    lgsqrlem1.3
    cz
    @37
    @29
    cL
    @36
    @28
    @7
    cA
    cz
    zring
    @36
    zringmpg
    zringbas
    mgpbas
    @37
    eqid
    #
    @33
    mhmmulg
    syl3anc
    wph
    @39
    cA
    @7
    cexp
    co
    #
    cL
    cfv
    #
    c1
    cL
    cfv
    #
    @3
    wph
    @38
    @44
    cL
    wph
    @7
    cA
    @35
    cmg
    cfv
    #
    co
    #
    @38
    @44
    wph
    cz
    @35
    csubmnd
    cfv
    wcel
    #
    @41
    @42
    @48
    @38
    wceq
    cz
    ccnfld
    csubrg
    cfv
    wcel
    @49
    wph
    zsubrg
    cz
    ccnfld
    @35
    @35
    eqid
    subrgsubm
    mp1i
    @34
    lgsqrlem1.3
    cz
    @47
    @37
    @35
    @36
    @7
    cA
    @47
    eqid
    @36
    eqid
    @43
    submmulg
    syl3anc
    wph
    cA
    cc
    wcel
    @41
    @48
    @44
    wceq
    wph
    cA
    lgsqrlem1.3
    zcnd
    @34
    cA
    @7
    cnfldexp
    syl2anc
    eqtr3d
    fveq2d
    wph
    @45
    @46
    wceq
    #
    cP
    @44
    c1
    cmin
    co
    cdvds
    wbr
    #
    wph
    @44
    cP
    cmo
    co
    c1
    cP
    cmo
    co
    wceq
    #
    @51
    lgsqrlem1.4
    wph
    cP
    cn
    wcel
    #
    @44
    cz
    wcel
    #
    c1
    cz
    wcel
    #
    @52
    @51
    wb
    wph
    @17
    @53
    @19
    cP
    prmnn
    syl
    #
    wph
    @42
    @41
    @54
    lgsqrlem1.3
    @34
    cA
    @7
    zexpcl
    syl2anc
    #
    wph
    1zzd
    #
    @44
    c1
    cP
    moddvds
    syl3anc
    mpbid
    wph
    cP
    cn0
    wcel
    @54
    @55
    @50
    @51
    wb
    wph
    cP
    @56
    nnnn0d
    @57
    @58
    @44
    c1
    cL
    cP
    cY
    lgsqr.y
    lgsqr.l
    zndvds
    syl3anc
    mpbird
    wph
    @21
    @46
    @3
    wceq
    @24
    zring
    cY
    c1
    cL
    @3
    zring1
    @3
    eqid
    #
    rhm1
    syl
    3eqtrd
    eqtr3d
    eqeq2d
    anbi2d
    mpbid
    wph
    @3
    cS
    cascl
    cfv
    #
    cfv
    #
    cB
    wcel
    #
    @0
    @61
    cO
    cfv
    #
    cfv
    #
    @3
    wceq
    #
    wa
    c.1
    cB
    wcel
    #
    @0
    c.1
    cO
    cfv
    #
    cfv
    #
    @3
    wceq
    #
    wa
    wph
    @60
    @12
    cS
    cY
    cB
    cO
    @3
    @0
    lgsqr.o
    lgsqr.s
    @13
    @60
    eqid
    #
    lgsqr.b
    @20
    wph
    @22
    @3
    @12
    wcel
    #
    @23
    @12
    cY
    @3
    @13
    @59
    ringidcl
    syl
    #
    @25
    evl1scad
    wph
    @62
    @66
    @65
    @69
    wph
    @61
    c.1
    cB
    wph
    @22
    @61
    c.1
    wceq
    @23
    @60
    cS
    cY
    @3
    c.1
    lgsqr.s
    @70
    @59
    lgsqr.u
    ply1scl1
    syl
    #
    eleq1d
    wph
    @64
    @68
    @3
    wph
    @0
    @63
    @67
    wph
    @61
    c.1
    cO
    @73
    fveq2d
    fveq1d
    eqeq1d
    anbi12d
    mpbid
    lgsqr.m
    @4
    eqid
    #
    evl1subd
    simprd
    syl5eq
    wph
    cY
    cgrp
    wcel
    #
    @71
    @5
    @6
    wceq
    wph
    @22
    @75
    @23
    cY
    ringgrp
    syl
    @72
    @12
    cY
    @4
    @3
    @6
    @13
    @6
    eqid
    @74
    grpsubid
    syl2anc
    eqtrd
end
