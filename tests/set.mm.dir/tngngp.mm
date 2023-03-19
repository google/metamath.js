include "cr.mm"
include "wf.mm"
include "cngp.mm"
include "wcel.mm"
include "cgrp.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "co.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "cds.mm"
include "cme.mm"
include "eqid.mm"
include "tngngp2.mm"
include "simprbda.mm"
include "cnm.mm"
include "c0g.mm"
include "cbs.mm"
include "simplr.mm"
include "simpr.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "reex.mm"
include "fex2.mm"
include "mp3an23.mm"
include "ad2antrr.mm"
include "tngbas.mm"
include "syl.mm"
include "eleqtrd.mm"
include "nmeq0.mm"
include "syl2anc.mm"
include "adantr.mm"
include "simpll.mm"
include "tngnm.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "tng0.mm"
include "eqeq2d.mm"
include "3bitr4d.mm"
include "csg.mm"
include "simpllr.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "nmmtri.mm"
include "syl3anc.mm"
include "syl5eqr.mm"
include "cplusg.mm"
include "tngplusg.mm"
include "grpsubpropd.mm"
include "syl5eq.mm"
include "oveqd.mm"
include "fveq12d.mm"
include "oveq12d.mm"
include "3brtr4d.mm"
include "ralrimiva.mm"
include "jca.mm"
include "simprl.mm"
include "simpl.mm"
include "ralimi.mm"
include "ad2antll.mm"
include "fveq2.mm"
include "eqeq1.mm"
include "bibi12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc2va.mm"
include "ancoms.mm"
include "tngngpd.mm"
include "impbida.mm"

theorem tngngp
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  let cG: class G
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let wph: wff ph
  assume tngngp.t: |- T = ( G toNrmGrp N )
  assume tngngp.x: |- X = ( Base ` G )
  assume tngngp.m: |- .- = ( -g ` G )
  assume tngngp.z: |- .0. = ( 0g ` G )

  disjoint x y
  disjoint .- x
  disjoint .- y
  disjoint N x
  disjoint N y
  disjoint T x
  disjoint T y
  disjoint X x
  disjoint X y
  disjoint .0. x
  disjoint .0. y
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint .- a
  disjoint b x
  disjoint b y
  disjoint .- b
  disjoint N a
  disjoint N b
  disjoint T a
  disjoint T b
  disjoint X a
  disjoint X b
  disjoint G a
  disjoint G b
  disjoint ph x
  disjoint ph y
  disjoint .0. a
  disjoint .0. b
  assert |- ( N : X --> RR -> ( T e. NrmGrp <-> ( G e. Grp /\ A. x e. X ( ( ( N ` x ) = 0 <-> x = .0. ) /\ A. y e. X ( N ` ( x .- y ) ) <_ ( ( N ` x ) + ( N ` y ) ) ) ) ) )

  proof
    cX
    cr
    cN
    wf
    #
    cT
    cngp
    wcel
    #
    cG
    cgrp
    wcel
    #
    vx
    cv
    #
    cN
    cfv
    #
    cc0
    wceq
    #
    @3
    c.0
    wceq
    #
    wb
    #
    @3
    vy
    cv
    #
    c.mi
    co
    #
    cN
    cfv
    #
    @4
    @8
    cN
    cfv
    #
    caddc
    co
    #
    cle
    wbr
    #
    vy
    cX
    wral
    #
    wa
    #
    vx
    cX
    wral
    #
    wa
    #
    @0
    @1
    wa
    #
    @2
    @16
    @0
    @1
    @2
    cT
    cds
    cfv
    #
    cX
    cme
    cfv
    wcel
    @19
    cT
    cG
    cN
    cX
    tngngp.t
    tngngp.x
    @19
    eqid
    tngngp2
    simprbda
    #
    @18
    @15
    vx
    cX
    @18
    @3
    cX
    wcel
    #
    wa
    #
    @7
    @14
    @22
    @3
    cT
    cnm
    cfv
    #
    cfv
    #
    cc0
    wceq
    #
    @3
    cT
    c0g
    cfv
    #
    wceq
    #
    @5
    @6
    @22
    @1
    @3
    cT
    cbs
    cfv
    #
    wcel
    #
    @25
    @27
    wb
    @0
    @1
    @21
    simplr
    @22
    @3
    cX
    @28
    @18
    @21
    simpr
    @22
    cN
    cvv
    wcel
    #
    cX
    @28
    wceq
    @0
    @30
    @1
    @21
    @0
    cX
    cvv
    wcel
    cr
    cvv
    wcel
    @30
    cX
    cG
    cbs
    cfv
    #
    cvv
    tngngp.x
    cG
    cbs
    fvex
    eqeltri
    reex
    cX
    cr
    cN
    cvv
    cvv
    fex2
    mp3an23
    ad2antrr
    #
    cX
    cT
    cG
    cN
    cvv
    tngngp.t
    tngngp.x
    tngbas
    syl
    #
    eleqtrd
    #
    @3
    cT
    @23
    @28
    @26
    @28
    eqid
    #
    @23
    eqid
    #
    @26
    eqid
    nmeq0
    syl2anc
    @22
    @4
    @24
    cc0
    @22
    @3
    cN
    @23
    @22
    @2
    @0
    cN
    @23
    wceq
    @18
    @2
    @21
    @20
    adantr
    @0
    @1
    @21
    simpll
    cr
    cT
    cG
    cN
    cX
    tngngp.t
    tngngp.x
    reex
    tngnm
    syl2anc
    #
    fveq1d
    #
    eqeq1d
    @22
    c.0
    @26
    @3
    @22
    @30
    c.0
    @26
    wceq
    @32
    cT
    cG
    cN
    cvv
    c.0
    tngngp.t
    tngngp.z
    tng0
    syl
    eqeq2d
    3bitr4d
    @22
    @13
    vy
    cX
    @22
    @8
    cX
    wcel
    #
    wa
    #
    @3
    @8
    cT
    csg
    cfv
    #
    co
    #
    @23
    cfv
    #
    @24
    @8
    @23
    cfv
    #
    caddc
    co
    #
    @10
    @12
    cle
    @40
    @1
    @29
    @8
    @28
    wcel
    #
    @43
    @45
    cle
    wbr
    @0
    @1
    @21
    @39
    simpllr
    @22
    @29
    @39
    @34
    adantr
    @22
    @39
    @46
    @22
    cX
    @28
    @8
    @33
    eleq2d
    biimpa
    @3
    @8
    cT
    @41
    @23
    @28
    @35
    @36
    @41
    eqid
    nmmtri
    syl3anc
    @22
    @10
    @43
    wceq
    @39
    @22
    @9
    @42
    cN
    @23
    @37
    @22
    c.mi
    @41
    @3
    @8
    @22
    c.mi
    cG
    csg
    cfv
    @41
    tngngp.m
    @22
    cG
    cT
    @22
    @31
    cX
    @28
    tngngp.x
    @33
    syl5eqr
    @22
    @30
    cG
    cplusg
    cfv
    #
    cT
    cplusg
    cfv
    wceq
    @32
    @47
    cT
    cG
    cN
    cvv
    tngngp.t
    @47
    eqid
    tngplusg
    syl
    grpsubpropd
    syl5eq
    oveqd
    fveq12d
    adantr
    @22
    @12
    @45
    wceq
    @39
    @22
    @4
    @24
    @11
    @44
    caddc
    @38
    @22
    @8
    cN
    @23
    @37
    fveq1d
    oveq12d
    adantr
    3brtr4d
    ralrimiva
    jca
    ralrimiva
    jca
    @0
    @17
    wa
    #
    va
    vb
    cT
    cG
    c.mi
    cN
    cX
    c.0
    tngngp.t
    tngngp.x
    tngngp.m
    tngngp.z
    @0
    @2
    @16
    simprl
    @0
    @17
    simpl
    @48
    @7
    vx
    cX
    wral
    #
    va
    cv
    #
    cX
    wcel
    #
    @50
    cN
    cfv
    #
    cc0
    wceq
    #
    @50
    c.0
    wceq
    #
    wb
    #
    @16
    @49
    @0
    @2
    @15
    @7
    vx
    cX
    @7
    @14
    simpl
    ralimi
    ad2antll
    @7
    @55
    vx
    @50
    cX
    @3
    @50
    wceq
    #
    @5
    @53
    @6
    @54
    @56
    @4
    @52
    cc0
    @3
    @50
    cN
    fveq2
    #
    eqeq1d
    @3
    @50
    c.0
    eqeq1
    bibi12d
    rspccva
    sylan
    @48
    @14
    vx
    cX
    wral
    #
    @51
    vb
    cv
    #
    cX
    wcel
    wa
    #
    @50
    @59
    c.mi
    co
    #
    cN
    cfv
    #
    @52
    @59
    cN
    cfv
    #
    caddc
    co
    #
    cle
    wbr
    #
    @16
    @58
    @0
    @2
    @15
    @14
    vx
    cX
    @7
    @14
    simpr
    ralimi
    ad2antll
    @60
    @58
    @65
    @13
    @65
    @50
    @8
    c.mi
    co
    #
    cN
    cfv
    #
    @52
    @11
    caddc
    co
    #
    cle
    wbr
    vx
    vy
    @50
    @59
    cX
    cX
    @56
    @10
    @67
    @12
    @68
    cle
    @56
    @9
    @66
    cN
    @3
    @50
    @8
    c.mi
    oveq1
    fveq2d
    @56
    @4
    @52
    @11
    caddc
    @57
    oveq1d
    breq12d
    @8
    @59
    wceq
    #
    @67
    @62
    @68
    @64
    cle
    @69
    @66
    @61
    cN
    @8
    @59
    @50
    c.mi
    oveq2
    fveq2d
    @69
    @11
    @63
    @52
    caddc
    @8
    @59
    cN
    fveq2
    oveq2d
    breq12d
    rspc2va
    ancoms
    sylan
    tngngpd
    impbida
end
