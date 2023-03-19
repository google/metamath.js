include "cr.mm"
include "wf.mm"
include "cngp.mm"
include "wcel.mm"
include "cgrp.mm"
include "cme.mm"
include "cfv.mm"
include "wa.mm"
include "ngpgrp.mm"
include "cvv.mm"
include "wb.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "reex.mm"
include "fex2.mm"
include "mp3an23.mm"
include "wceq.mm"
include "a1i.mm"
include "tngbas.mm"
include "cv.mm"
include "cplusg.mm"
include "eqid.mm"
include "tngplusg.mm"
include "oveqdr.mm"
include "grppropd.mm"
include "syl.mm"
include "syl5ibr.mm"
include "imp.mm"
include "cxp.mm"
include "cres.mm"
include "cmt.mm"
include "ngpms.mm"
include "adantl.mm"
include "msmet2.mm"
include "wfn.mm"
include "csg.mm"
include "ccom.mm"
include "grpsubf.mm"
include "fco.mm"
include "syldan.mm"
include "cds.mm"
include "adantr.mm"
include "tngds.mm"
include "syl6reqr.mm"
include "feq1d.mm"
include "mpbird.mm"
include "ffn.mm"
include "fnresdm.mm"
include "3syl.mm"
include "sqxpeqd.mm"
include "reseq2d.mm"
include "eqtr3d.mm"
include "fveq2d.mm"
include "3eltr4d.mm"
include "jca.mm"
include "cnm.mm"
include "wss.mm"
include "biimpa.mm"
include "adantrr.mm"
include "ctopn.mm"
include "cmopn.mm"
include "simprr.mm"
include "eleqtrd.mm"
include "metf.mm"
include "eqeltrd.mm"
include "simprl.mm"
include "tngtopn.mm"
include "syl2anc.mm"
include "eqtr2d.mm"
include "reseq1i.mm"
include "isms2.mm"
include "sylanbrc.mm"
include "simpl.mm"
include "tngnm.mm"
include "grpsubpropd.mm"
include "coeq12d.mm"
include "eqimss.mm"
include "isngp.mm"
include "syl3anbrc.mm"
include "impbida.mm"

theorem tngngp2
  let cD: class D
  let cT: class T
  let cG: class G
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume tngngp2.t: |- T = ( G toNrmGrp N )
  assume tngngp2.x: |- X = ( Base ` G )
  assume tngngp2.d: |- D = ( dist ` T )


  assert |- ( N : X --> RR -> ( T e. NrmGrp <-> ( G e. Grp /\ D e. ( Met ` X ) ) ) )

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
    cD
    cX
    cme
    cfv
    #
    wcel
    #
    wa
    #
    @0
    @1
    wa
    #
    @2
    @4
    @0
    @1
    @2
    @1
    @2
    @0
    cT
    cgrp
    wcel
    #
    cT
    ngpgrp
    @0
    cN
    cvv
    wcel
    #
    @2
    @7
    wb
    @0
    cX
    cvv
    wcel
    cr
    cvv
    wcel
    @8
    cX
    cG
    cbs
    cfv
    #
    cvv
    tngngp2.x
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
    #
    @8
    vx
    vy
    cX
    cG
    cT
    cX
    @9
    wceq
    @8
    tngngp2.x
    a1i
    #
    cX
    cT
    cG
    cN
    cvv
    tngngp2.t
    tngngp2.x
    tngbas
    #
    @8
    vx
    cv
    cX
    wcel
    vy
    cv
    cX
    wcel
    wa
    vx
    vy
    cG
    cplusg
    cfv
    #
    cT
    cplusg
    cfv
    @13
    cT
    cG
    cN
    cvv
    tngngp2.t
    @13
    eqid
    tngplusg
    #
    oveqdr
    grppropd
    syl
    #
    syl5ibr
    imp
    #
    @6
    cD
    cT
    cbs
    cfv
    #
    @17
    cxp
    #
    cres
    #
    @17
    cme
    cfv
    #
    cD
    @3
    @6
    cT
    cmt
    wcel
    #
    @19
    @20
    wcel
    #
    @1
    @21
    @0
    cT
    ngpms
    adantl
    cD
    cT
    @17
    @17
    eqid
    #
    tngngp2.d
    msmet2
    syl
    @6
    cD
    cX
    cX
    cxp
    #
    cres
    #
    cD
    @19
    @6
    @24
    cr
    cD
    wf
    #
    cD
    @24
    wfn
    @25
    cD
    wceq
    @6
    @26
    @24
    cr
    cN
    cG
    csg
    cfv
    #
    ccom
    #
    wf
    #
    @0
    @1
    @24
    cX
    @27
    wf
    #
    @29
    @6
    @2
    @30
    @16
    cX
    cG
    @27
    tngngp2.x
    @27
    eqid
    #
    grpsubf
    syl
    @24
    cX
    cr
    cN
    @27
    fco
    syldan
    @6
    @24
    cr
    cD
    @28
    @6
    @28
    cT
    cds
    cfv
    #
    cD
    @6
    @8
    @28
    @32
    wceq
    #
    @0
    @8
    @1
    @10
    adantr
    #
    cT
    cG
    @27
    cN
    cvv
    tngngp2.t
    @31
    tngds
    #
    syl
    tngngp2.d
    syl6reqr
    feq1d
    mpbird
    @24
    cr
    cD
    ffn
    @24
    cD
    fnresdm
    3syl
    @6
    @24
    @18
    cD
    @6
    cX
    @17
    @6
    @8
    cX
    @17
    wceq
    #
    @34
    @12
    syl
    #
    sqxpeqd
    reseq2d
    eqtr3d
    @6
    cX
    @17
    cme
    @37
    fveq2d
    3eltr4d
    jca
    @0
    @5
    wa
    #
    @7
    @21
    cT
    cnm
    cfv
    #
    cT
    csg
    cfv
    #
    ccom
    #
    @32
    wss
    #
    @1
    @0
    @2
    @7
    @4
    @0
    @2
    @7
    @15
    biimpa
    adantrr
    @38
    @22
    cT
    ctopn
    cfv
    #
    @19
    cmopn
    cfv
    #
    wceq
    @21
    @38
    @19
    cD
    @20
    @38
    @18
    cr
    cD
    wf
    #
    cD
    @18
    wfn
    @19
    cD
    wceq
    @38
    cD
    @20
    wcel
    @45
    @38
    cD
    @3
    @20
    @0
    @2
    @4
    simprr
    @38
    cX
    @17
    cme
    @38
    @8
    @36
    @0
    @8
    @5
    @10
    adantr
    #
    @12
    syl
    fveq2d
    eleqtrd
    #
    cD
    @17
    metf
    syl
    @18
    cr
    cD
    ffn
    @18
    cD
    fnresdm
    3syl
    #
    @47
    eqeltrd
    @38
    @44
    cD
    cmopn
    cfv
    #
    @43
    @38
    @19
    cD
    cmopn
    @48
    fveq2d
    @38
    @2
    @8
    @49
    @43
    wceq
    @0
    @2
    @4
    simprl
    #
    @46
    cD
    cT
    cG
    @49
    cN
    cgrp
    cvv
    tngngp2.t
    tngngp2.d
    @49
    eqid
    tngtopn
    syl2anc
    eqtr2d
    @19
    @43
    cT
    @17
    @43
    eqid
    @23
    cD
    @32
    @18
    tngngp2.d
    reseq1i
    isms2
    sylanbrc
    @38
    @41
    @32
    wceq
    @42
    @38
    @28
    @41
    @32
    @38
    cN
    @39
    @27
    @40
    @38
    @2
    @0
    cN
    @39
    wceq
    @50
    @0
    @5
    simpl
    cr
    cT
    cG
    cN
    cX
    tngngp2.t
    tngngp2.x
    reex
    tngnm
    syl2anc
    @38
    @8
    @27
    @40
    wceq
    @46
    @8
    cG
    cT
    @8
    cX
    @9
    @17
    @11
    @12
    eqtr3d
    @14
    grpsubpropd
    syl
    coeq12d
    @38
    @8
    @33
    @46
    @35
    syl
    eqtr3d
    @41
    @32
    eqimss
    syl
    @32
    cT
    @40
    @39
    @39
    eqid
    @40
    eqid
    @32
    eqid
    isngp
    syl3anbrc
    impbida
end
