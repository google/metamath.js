include "cv.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "cres.mm"
include "wceq.mm"
include "cin.mm"
include "wrex.mm"
include "cmpt.mm"
include "crn.mm"
include "cn.mm"
include "cdif.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cun.mm"
include "ccnv.mm"
include "cima.mm"
include "cfn.mm"
include "wss.mm"
include "wf.mm"
include "c0.mm"
include "elmapi.mm"
include "adantr.mm"
include "c0ex.mm"
include "fconst.mm"
include "a1i.mm"
include "disjdif.mm"
include "fun.mm"
include "syl21anc.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "undif.mm"
include "mpbi.mm"
include "0nn0.mm"
include "snssi.mm"
include "ax-mp.mm"
include "ssequn2.mm"
include "feq23i.mm"
include "sylib.mm"
include "nn0ex.mm"
include "nnex.mm"
include "elmap.mm"
include "sylibr.mm"
include "cnvun.mm"
include "imaeq1i.mm"
include "imaundir.mm"
include "eqtri.mm"
include "vex.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "eleq1d.mm"
include "elab2.mm"
include "biimpi.mm"
include "adantl.mm"
include "cdm.mm"
include "cnvxp.mm"
include "dmeqi.mm"
include "wne.mm"
include "2nn.mm"
include "cz.mm"
include "2z.mm"
include "iddvds.mm"
include "breq2.mm"
include "notbid.mm"
include "elrab2.mm"
include "simprbi.mm"
include "mt2.mm"
include "eldif.mm"
include "mpbir2an.mm"
include "ne0i.mm"
include "dmxp.mm"
include "mp2b.mm"
include "ineq1i.mm"
include "incom.mm"
include "0nnn.mm"
include "disjsn.mm"
include "mpbir.mm"
include "3eqtr2i.mm"
include "imadisj.mm"
include "0fin.mm"
include "eqeltri.mm"
include "unfi.mm"
include "sylancl.mm"
include "syl5eqel.mm"
include "cnvimass.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "0ss.mm"
include "unssd.mm"
include "syl5eqss.mm"
include "eulerpartlemt0.mm"
include "syl3anbrc.mm"
include "resundir.mm"
include "wfn.mm"
include "ffn.mm"
include "fnresdm.mm"
include "wb.mm"
include "fnconstg.mm"
include "fnresdisj.mm"
include "uneq12d.mm"
include "3syl.mm"
include "un0.mm"
include "syl6eq.mm"
include "syl5req.mm"
include "reseq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "simpr.mm"
include "w3a.mm"
include "simpl.mm"
include "simp1d.mm"
include "fssres.mm"
include "rabex2.mm"
include "eqeltrd.mm"
include "wfun.mm"
include "ffun.mm"
include "respreima.mm"
include "simp2d.mm"
include "infi.mm"
include "resex.mm"
include "jca.mm"
include "rexlimiva.mm"
include "impbii.mm"
include "abbii.mm"
include "df-in.mm"
include "eqid.mm"
include "rnmpt.mm"
include "3eqtr4i.mm"

theorem eulerpartlemt
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let cP: class P
  let cR: class R
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cH: class H
  let cJ: class J
  let cM: class M
  let cN: class N
  let cO: class O
  let vr: setvar r
  let vo: setvar o
  assume eulerpart.p: |- P = { f e. ( NN0 ^m NN ) | ( ( `' f " NN ) e. Fin /\ sum_ k e. NN ( ( f ` k ) x. k ) = N ) }
  assume eulerpart.o: |- O = { g e. P | A. n e. ( `' g " NN ) -. 2 || n }
  assume eulerpart.d: |- D = { g e. P | A. n e. NN ( g ` n ) <_ 1 }
  assume eulerpart.j: |- J = { z e. NN | -. 2 || z }
  assume eulerpart.f: |- F = ( x e. J , y e. NN0 |-> ( ( 2 ^ y ) x. x ) )
  assume eulerpart.h: |- H = { r e. ( ( ~P NN0 i^i Fin ) ^m J ) | ( r supp (/) ) e. Fin }
  assume eulerpart.m: |- M = ( r e. H |-> { <. x , y >. | ( x e. J /\ y e. ( r ` x ) ) } )
  assume eulerpart.r: |- R = { f | ( `' f " NN ) e. Fin }
  assume eulerpart.t: |- T = { f e. ( NN0 ^m NN ) | ( `' f " NN ) C_ J }

  disjoint f m
  disjoint J f
  disjoint J m
  disjoint R m
  disjoint T m
  disjoint f o
  disjoint m o
  disjoint J o
  disjoint R o
  disjoint T o
  assert |- ( ( NN0 ^m J ) i^i R ) = ran ( m e. ( T i^i R ) |-> ( m |` J ) )

  proof
    vo
    cv
    #
    cn0
    cJ
    cmap
    co
    #
    wcel
    #
    @0
    cR
    wcel
    #
    wa
    #
    vo
    cab
    @0
    vm
    cv
    #
    cJ
    cres
    #
    wceq
    #
    vm
    cT
    cR
    cin
    #
    wrex
    #
    vo
    cab
    @1
    cR
    cin
    vm
    @8
    @6
    cmpt
    #
    crn
    @4
    @9
    vo
    @4
    @9
    @4
    @0
    cn
    cJ
    cdif
    #
    cc0
    csn
    #
    cxp
    #
    cun
    #
    @8
    wcel
    #
    @0
    @14
    cJ
    cres
    #
    wceq
    #
    @9
    @4
    @14
    cn0
    cn
    cmap
    co
    #
    wcel
    #
    @14
    ccnv
    #
    cn
    cima
    #
    cfn
    wcel
    @21
    cJ
    wss
    @15
    @4
    cn
    cn0
    @14
    wf
    #
    @19
    @4
    cJ
    @11
    cun
    #
    cn0
    @12
    cun
    #
    @14
    wf
    #
    @22
    @4
    cJ
    cn0
    @0
    wf
    #
    @11
    @12
    @13
    wf
    #
    cJ
    @11
    cin
    #
    c0
    wceq
    #
    @25
    @2
    @26
    @3
    @0
    cn0
    cJ
    elmapi
    adantr
    #
    @27
    @4
    @11
    cc0
    c0ex
    fconst
    a1i
    @29
    @4
    cJ
    cn
    disjdif
    #
    a1i
    cJ
    @11
    cn0
    @12
    @0
    @13
    fun
    syl21anc
    @23
    @24
    cn
    cn0
    @14
    cJ
    cn
    wss
    #
    @23
    cn
    wceq
    cJ
    c2
    vz
    cv
    #
    cdvds
    wbr
    #
    wn
    #
    vz
    cn
    crab
    cn
    eulerpart.j
    @35
    vz
    cn
    ssrab2
    eqsstri
    #
    cJ
    cn
    undif
    mpbi
    @12
    cn0
    wss
    #
    @24
    cn0
    wceq
    cc0
    cn0
    wcel
    #
    @37
    0nn0
    cc0
    cn0
    snssi
    ax-mp
    @12
    cn0
    ssequn2
    mpbi
    feq23i
    sylib
    cn0
    cn
    @14
    nn0ex
    nnex
    elmap
    sylibr
    @4
    @21
    @0
    ccnv
    #
    cn
    cima
    #
    @13
    ccnv
    #
    cn
    cima
    #
    cun
    #
    cfn
    @21
    @39
    @41
    cun
    #
    cn
    cima
    @43
    @20
    @44
    cn
    @0
    @13
    cnvun
    imaeq1i
    @39
    @41
    cn
    imaundir
    eqtri
    #
    @4
    @40
    cfn
    wcel
    #
    @42
    cfn
    wcel
    @43
    cfn
    wcel
    @3
    @46
    @2
    @3
    @46
    vf
    cv
    #
    ccnv
    #
    cn
    cima
    #
    cfn
    wcel
    #
    @46
    vf
    @0
    cR
    vo
    vex
    @47
    @0
    wceq
    #
    @49
    @40
    cfn
    @51
    @48
    @39
    cn
    @47
    @0
    cnveq
    imaeq1d
    eleq1d
    eulerpart.r
    elab2
    biimpi
    adantl
    @42
    c0
    cfn
    @42
    c0
    wceq
    @41
    cdm
    #
    cn
    cin
    #
    c0
    wceq
    @53
    @12
    cn
    cin
    cn
    @12
    cin
    #
    c0
    @52
    @12
    cn
    @52
    @12
    @11
    cxp
    #
    cdm
    #
    @12
    @41
    @55
    @11
    @12
    cnvxp
    dmeqi
    c2
    @11
    wcel
    #
    @11
    c0
    wne
    @56
    @12
    wceq
    @57
    c2
    cn
    wcel
    #
    c2
    cJ
    wcel
    #
    wn
    2nn
    @59
    c2
    c2
    cdvds
    wbr
    #
    c2
    cz
    wcel
    @60
    2z
    c2
    iddvds
    ax-mp
    @59
    @58
    @60
    wn
    #
    @35
    @61
    vz
    c2
    cn
    cJ
    @33
    c2
    wceq
    @34
    @60
    @33
    c2
    c2
    cdvds
    breq2
    notbid
    eulerpart.j
    elrab2
    simprbi
    mt2
    c2
    cn
    cJ
    eldif
    mpbir2an
    @11
    c2
    ne0i
    @12
    @11
    dmxp
    mp2b
    eqtri
    ineq1i
    cn
    @12
    incom
    @54
    c0
    wceq
    cc0
    cn
    wcel
    wn
    0nnn
    cn
    cc0
    disjsn
    mpbir
    3eqtr2i
    @41
    cn
    imadisj
    mpbir
    #
    0fin
    eqeltri
    @40
    @42
    unfi
    sylancl
    syl5eqel
    @4
    @21
    @43
    cJ
    @45
    @4
    @40
    @42
    cJ
    @4
    @0
    cdm
    #
    @40
    cJ
    @0
    cn
    cnvimass
    @4
    @26
    @63
    cJ
    wceq
    @30
    cJ
    cn0
    @0
    fdm
    syl
    syl5sseq
    @42
    cJ
    wss
    @4
    @42
    c0
    cJ
    @62
    cJ
    0ss
    eqsstri
    a1i
    unssd
    syl5eqss
    vx
    vy
    vz
    @14
    cD
    cP
    cR
    cT
    vf
    vg
    vk
    vn
    cF
    cH
    cJ
    cM
    cN
    cO
    vr
    eulerpart.p
    eulerpart.o
    eulerpart.d
    eulerpart.j
    eulerpart.f
    eulerpart.h
    eulerpart.m
    eulerpart.r
    eulerpart.t
    eulerpartlemt0
    syl3anbrc
    @4
    @16
    @0
    cJ
    cres
    #
    @13
    cJ
    cres
    #
    cun
    #
    @0
    @0
    @13
    cJ
    resundir
    @4
    @66
    @0
    c0
    cun
    #
    @0
    @4
    @26
    @0
    cJ
    wfn
    #
    @66
    @67
    wceq
    @30
    cJ
    cn0
    @0
    ffn
    @68
    @64
    @0
    @65
    c0
    cJ
    @0
    fnresdm
    @65
    c0
    wceq
    #
    @68
    @11
    cJ
    cin
    #
    c0
    wceq
    #
    @69
    @70
    @28
    c0
    @11
    cJ
    incom
    @31
    eqtri
    @38
    @13
    @11
    wfn
    @71
    @69
    wb
    0nn0
    @11
    cc0
    cn0
    fnconstg
    @11
    cJ
    @13
    fnresdisj
    mp2b
    mpbi
    a1i
    uneq12d
    3syl
    @0
    un0
    syl6eq
    syl5req
    @7
    @17
    vm
    @14
    @8
    @5
    @14
    wceq
    @6
    @16
    @0
    @5
    @14
    cJ
    reseq1
    eqeq2d
    rspcev
    syl2anc
    @7
    @4
    vm
    @8
    @5
    @8
    wcel
    #
    @7
    wa
    #
    @2
    @3
    @73
    @0
    @6
    @1
    @72
    @7
    simpr
    #
    @73
    cJ
    cn0
    @6
    wf
    #
    @6
    @1
    wcel
    @73
    cn
    cn0
    @5
    wf
    #
    @32
    @75
    @73
    @5
    @18
    wcel
    #
    @76
    @73
    @77
    @5
    ccnv
    cn
    cima
    #
    cfn
    wcel
    #
    @78
    cJ
    wss
    #
    @73
    @72
    @77
    @79
    @80
    w3a
    @72
    @7
    simpl
    vx
    vy
    vz
    @5
    cD
    cP
    cR
    cT
    vf
    vg
    vk
    vn
    cF
    cH
    cJ
    cM
    cN
    cO
    vr
    eulerpart.p
    eulerpart.o
    eulerpart.d
    eulerpart.j
    eulerpart.f
    eulerpart.h
    eulerpart.m
    eulerpart.r
    eulerpart.t
    eulerpartlemt0
    sylib
    #
    simp1d
    cn0
    cn
    @5
    nn0ex
    nnex
    elmap
    sylib
    #
    @36
    cn
    cn0
    cJ
    @5
    fssres
    sylancl
    cn0
    cJ
    @6
    nn0ex
    @35
    vz
    cn
    cJ
    eulerpart.j
    nnex
    rabex2
    elmap
    sylibr
    eqeltrd
    @73
    @0
    @6
    cR
    @74
    @73
    @6
    ccnv
    #
    cn
    cima
    #
    cfn
    wcel
    #
    @6
    cR
    wcel
    @73
    @84
    @78
    cJ
    cin
    #
    cfn
    @73
    @76
    @5
    wfun
    @84
    @86
    wceq
    @82
    cn
    cn0
    @5
    ffun
    cn
    cJ
    @5
    respreima
    3syl
    @73
    @79
    @86
    cfn
    wcel
    @73
    @77
    @79
    @80
    @81
    simp2d
    @78
    cJ
    infi
    syl
    eqeltrd
    @50
    @85
    vf
    @6
    cR
    @5
    cJ
    vm
    vex
    resex
    @47
    @6
    wceq
    #
    @49
    @84
    cfn
    @87
    @48
    @83
    cn
    @47
    @6
    cnveq
    imaeq1d
    eleq1d
    eulerpart.r
    elab2
    sylibr
    eqeltrd
    jca
    rexlimiva
    impbii
    abbii
    vo
    @1
    cR
    df-in
    vm
    vo
    @8
    @6
    @10
    @10
    eqid
    rnmpt
    3eqtr4i
end
