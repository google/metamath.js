include "c2.mm"
include "cv.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "cima.mm"
include "cres.mm"
include "cop.mm"
include "cvtxdg.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "wceq.mm"
include "c0.mm"
include "cpr.mm"
include "cif.mm"
include "cupgr.mm"
include "eqid.mm"
include "eupthvdres.mm"
include "fveq1d.mm"
include "breq2d.mm"
include "notbid.mm"
include "rabbidv.mm"
include "cn0.mm"
include "wcel.mm"
include "ceupth.mm"
include "cwlks.mm"
include "eupthiswlk.mm"
include "wlkcl.mm"
include "3syl.mm"
include "cle.mm"
include "nn0re.mm"
include "leidd.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "breq1.mm"
include "oveq2.mm"
include "imaeq2d.mm"
include "reseq2d.mm"
include "opeq2d.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "preq2d.mm"
include "ifbieq2d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "eupth2lemb.mm"
include "iftruei.mm"
include "syl6eqr.mm"
include "a1d.mm"
include "eupth2lems.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "mpid.mm"
include "mpcom.mm"
include "eqtr3d.mm"

theorem eupth2
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let vy: setvar y
  let vn: setvar n
  let vm: setvar m
  assume eupth2.v: |- V = ( Vtx ` G )
  assume eupth2.i: |- I = ( iEdg ` G )
  assume eupth2.g: |- ( ph -> G e. UPGraph )
  assume eupth2.f: |- ( ph -> Fun I )
  assume eupth2.p: |- ( ph -> F ( EulerPaths ` G ) P )

  disjoint ph x
  disjoint F x
  disjoint I x
  disjoint V x
  disjoint F y
  disjoint x y
  disjoint I y
  disjoint P y
  disjoint V y
  disjoint n x
  disjoint n y
  disjoint ph y
  disjoint F m
  disjoint F n
  disjoint m n
  disjoint m x
  disjoint I m
  disjoint I n
  disjoint P m
  disjoint P n
  disjoint V m
  disjoint V n
  disjoint m ph
  disjoint n ph
  assert |- ( ph -> { x e. V | -. 2 || ( ( VtxDeg ` G ) ` x ) } = if ( ( P ` 0 ) = ( P ` ( # ` F ) ) , (/) , { ( P ` 0 ) , ( P ` ( # ` F ) ) } ) )

  proof
    wph
    c2
    vx
    cv
    #
    cV
    cI
    cF
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    cima
    #
    cres
    #
    cop
    #
    cvtxdg
    cfv
    #
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    vx
    cV
    crab
    #
    c2
    @0
    cG
    cvtxdg
    cfv
    #
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    vx
    cV
    crab
    cc0
    cP
    cfv
    #
    @1
    cP
    cfv
    #
    wceq
    #
    c0
    @15
    @16
    cpr
    #
    cif
    #
    wph
    @9
    @14
    vx
    cV
    wph
    @8
    @13
    wph
    @7
    @12
    c2
    cdvds
    wph
    @0
    @6
    @11
    wph
    cP
    cF
    cG
    @5
    cI
    cV
    cupgr
    eupth2.v
    eupth2.i
    eupth2.g
    eupth2.f
    eupth2.p
    @5
    eqid
    eupthvdres
    fveq1d
    breq2d
    notbid
    rabbidv
    @1
    cn0
    wcel
    #
    wph
    @10
    @19
    wceq
    #
    wph
    cF
    cP
    cG
    ceupth
    cfv
    wbr
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    @20
    eupth2.p
    cP
    cF
    cG
    eupthiswlk
    cP
    cF
    cG
    wlkcl
    3syl
    @20
    wph
    @1
    @1
    cle
    wbr
    #
    @21
    @20
    @1
    @1
    nn0re
    leidd
    wph
    vm
    cv
    #
    @1
    cle
    wbr
    #
    c2
    @0
    cV
    cI
    cF
    cc0
    @23
    cfzo
    co
    #
    cima
    #
    cres
    #
    cop
    #
    cvtxdg
    cfv
    #
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    vx
    cV
    crab
    #
    @15
    @23
    cP
    cfv
    #
    wceq
    #
    c0
    @15
    @34
    cpr
    #
    cif
    #
    wceq
    #
    wi
    #
    wi
    wph
    cc0
    @1
    cle
    wbr
    #
    c2
    @0
    cV
    cI
    cF
    cc0
    cc0
    cfzo
    co
    #
    cima
    #
    cres
    #
    cop
    #
    cvtxdg
    cfv
    #
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    vx
    cV
    crab
    #
    @15
    @15
    wceq
    #
    c0
    @15
    @15
    cpr
    #
    cif
    #
    wceq
    #
    wi
    #
    wi
    wph
    vn
    cv
    #
    @1
    cle
    wbr
    #
    c2
    @0
    cV
    cI
    cF
    cc0
    @55
    cfzo
    co
    #
    cima
    #
    cres
    #
    cop
    #
    cvtxdg
    cfv
    #
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    vx
    cV
    crab
    #
    @15
    @55
    cP
    cfv
    #
    wceq
    #
    c0
    @15
    @66
    cpr
    #
    cif
    #
    wceq
    #
    wi
    #
    wi
    wph
    @55
    c1
    caddc
    co
    #
    @1
    cle
    wbr
    #
    c2
    @0
    cV
    cI
    cF
    cc0
    @72
    cfzo
    co
    #
    cima
    #
    cres
    #
    cop
    #
    cvtxdg
    cfv
    #
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    vx
    cV
    crab
    #
    @15
    @72
    cP
    cfv
    #
    wceq
    #
    c0
    @15
    @83
    cpr
    #
    cif
    #
    wceq
    #
    wi
    #
    wi
    wph
    @22
    @21
    wi
    #
    wi
    vm
    vn
    @1
    @23
    cc0
    wceq
    #
    @39
    @54
    wph
    @90
    @24
    @40
    @38
    @53
    @23
    cc0
    @1
    cle
    breq1
    @90
    @33
    @49
    @37
    @52
    @90
    @32
    @48
    vx
    cV
    @90
    @31
    @47
    @90
    @30
    @46
    c2
    cdvds
    @90
    @0
    @29
    @45
    @90
    @28
    @44
    cvtxdg
    @90
    @27
    @43
    cV
    @90
    @26
    @42
    cI
    @90
    @25
    @41
    cF
    @23
    cc0
    cc0
    cfzo
    oveq2
    imaeq2d
    reseq2d
    opeq2d
    fveq2d
    fveq1d
    breq2d
    notbid
    rabbidv
    @90
    @35
    @50
    @36
    @51
    c0
    @90
    @34
    @15
    @15
    @23
    cc0
    cP
    fveq2
    #
    eqeq2d
    @90
    @34
    @15
    @15
    @91
    preq2d
    ifbieq2d
    eqeq12d
    imbi12d
    imbi2d
    @23
    @55
    wceq
    #
    @39
    @71
    wph
    @92
    @24
    @56
    @38
    @70
    @23
    @55
    @1
    cle
    breq1
    @92
    @33
    @65
    @37
    @69
    @92
    @32
    @64
    vx
    cV
    @92
    @31
    @63
    @92
    @30
    @62
    c2
    cdvds
    @92
    @0
    @29
    @61
    @92
    @28
    @60
    cvtxdg
    @92
    @27
    @59
    cV
    @92
    @26
    @58
    cI
    @92
    @25
    @57
    cF
    @23
    @55
    cc0
    cfzo
    oveq2
    imaeq2d
    reseq2d
    opeq2d
    fveq2d
    fveq1d
    breq2d
    notbid
    rabbidv
    @92
    @35
    @67
    @36
    @68
    c0
    @92
    @34
    @66
    @15
    @23
    @55
    cP
    fveq2
    #
    eqeq2d
    @92
    @34
    @66
    @15
    @93
    preq2d
    ifbieq2d
    eqeq12d
    imbi12d
    imbi2d
    @23
    @72
    wceq
    #
    @39
    @88
    wph
    @94
    @24
    @73
    @38
    @87
    @23
    @72
    @1
    cle
    breq1
    @94
    @33
    @82
    @37
    @86
    @94
    @32
    @81
    vx
    cV
    @94
    @31
    @80
    @94
    @30
    @79
    c2
    cdvds
    @94
    @0
    @29
    @78
    @94
    @28
    @77
    cvtxdg
    @94
    @27
    @76
    cV
    @94
    @26
    @75
    cI
    @94
    @25
    @74
    cF
    @23
    @72
    cc0
    cfzo
    oveq2
    imaeq2d
    reseq2d
    opeq2d
    fveq2d
    fveq1d
    breq2d
    notbid
    rabbidv
    @94
    @35
    @84
    @36
    @85
    c0
    @94
    @34
    @83
    @15
    @23
    @72
    cP
    fveq2
    #
    eqeq2d
    @94
    @34
    @83
    @15
    @95
    preq2d
    ifbieq2d
    eqeq12d
    imbi12d
    imbi2d
    @23
    @1
    wceq
    #
    @39
    @89
    wph
    @96
    @24
    @22
    @38
    @21
    @23
    @1
    @1
    cle
    breq1
    @96
    @33
    @10
    @37
    @19
    @96
    @32
    @9
    vx
    cV
    @96
    @31
    @8
    @96
    @30
    @7
    c2
    cdvds
    @96
    @0
    @29
    @6
    @96
    @28
    @5
    cvtxdg
    @96
    @27
    @4
    cV
    @96
    @26
    @3
    cI
    @96
    @25
    @2
    cF
    @23
    @1
    cc0
    cfzo
    oveq2
    imaeq2d
    reseq2d
    opeq2d
    fveq2d
    fveq1d
    breq2d
    notbid
    rabbidv
    @96
    @35
    @17
    @36
    @18
    c0
    @96
    @34
    @16
    @15
    @23
    @1
    cP
    fveq2
    #
    eqeq2d
    @96
    @34
    @16
    @15
    @97
    preq2d
    ifbieq2d
    eqeq12d
    imbi12d
    imbi2d
    wph
    @53
    @40
    wph
    @49
    c0
    @52
    wph
    vx
    cP
    cF
    cG
    cI
    cV
    eupth2.v
    eupth2.i
    eupth2.g
    eupth2.f
    eupth2.p
    eupth2lemb
    @50
    c0
    @51
    @15
    eqid
    iftruei
    syl6eqr
    a1d
    @55
    cn0
    wcel
    #
    wph
    @71
    @88
    wph
    @98
    @71
    @88
    wi
    wph
    vx
    cP
    vn
    cF
    cG
    cI
    cV
    eupth2.v
    eupth2.i
    eupth2.g
    eupth2.f
    eupth2.p
    eupth2lems
    expcom
    a2d
    nn0ind
    mpid
    mpcom
    eqtr3d
end
