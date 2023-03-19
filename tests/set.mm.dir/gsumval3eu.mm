include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "wf1o.mm"
include "ccom.mm"
include "cseq.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "weu.mm"
include "cn.mm"
include "wcel.mm"
include "c0.mm"
include "wn.mm"
include "neneqd.mm"
include "cfn.mm"
include "wo.mm"
include "fz1f1o.mm"
include "syl.mm"
include "ord.mm"
include "mpd.mm"
include "simprd.mm"
include "excom.mm"
include "exancom.mm"
include "fvex.mm"
include "biidd.mm"
include "ceqsexv.mm"
include "bitri.mm"
include "exbii.mm"
include "sylibr.mm"
include "eeanv.mm"
include "an4.mm"
include "crn.mm"
include "ccnv.mm"
include "cmnd.mm"
include "adantr.mm"
include "mndcl.mm"
include "3expb.mm"
include "sylan.mm"
include "wss.mm"
include "sselda.mm"
include "adantrr.mm"
include "simprr.mm"
include "cntzi.mm"
include "syl2anc.mm"
include "w3a.mm"
include "mndass.mm"
include "cuz.mm"
include "simpld.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "wf.mm"
include "frn.mm"
include "f1ocnv.mm"
include "simprl.mm"
include "f1oco.mm"
include "f1of.mm"
include "fvco3.mm"
include "wfn.mm"
include "ffn.mm"
include "fssd.mm"
include "ffvelrnda.mm"
include "fnfvelrn.mm"
include "eqeltrd.mm"
include "fveq2d.mm"
include "f1ocnvfv2.mm"
include "eqtr2d.mm"
include "syldan.mm"
include "3eqtr4d.mm"
include "seqf1o.mm"
include "eqeq12.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "syl5bir.mm"
include "exlimdvv.mm"
include "alrimivv.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "f1oeq1.mm"
include "coeq2.mm"
include "seqeq3d.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "cbvexv.mm"
include "syl6bb.mm"
include "eu4.mm"
include "sylanbrc.mm"

theorem gsumval3eu
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let cZ: class Z
  let vg: setvar g
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  let cH: class H
  assume gsumval3.b: |- B = ( Base ` G )
  assume gsumval3.0: |- .0. = ( 0g ` G )
  assume gsumval3.p: |- .+ = ( +g ` G )
  assume gsumval3.z: |- Z = ( Cntz ` G )
  assume gsumval3.g: |- ( ph -> G e. Mnd )
  assume gsumval3.a: |- ( ph -> A e. V )
  assume gsumval3.f: |- ( ph -> F : A --> B )
  assume gsumval3.c: |- ( ph -> ran F C_ ( Z ` ran F ) )
  assume gsumval3a.t: |- ( ph -> W e. Fin )
  assume gsumval3a.n: |- ( ph -> W =/= (/) )
  assume gsumval3a.s: |- ( ph -> W C_ A )

  disjoint f x
  disjoint .+ f
  disjoint .+ x
  disjoint A f
  disjoint A x
  disjoint f ph
  disjoint ph x
  disjoint .0. x
  disjoint G f
  disjoint G x
  disjoint V x
  disjoint B f
  disjoint B x
  disjoint F f
  disjoint F x
  disjoint W f
  disjoint W x
  disjoint f g
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f y
  disjoint f z
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint .+ g
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint .+ k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint .+ m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint .+ n
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint .+ y
  disjoint .+ z
  disjoint A g
  disjoint A k
  disjoint A m
  disjoint A n
  disjoint A y
  disjoint A z
  disjoint g ph
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph y
  disjoint ph z
  disjoint .0. g
  disjoint .0. y
  disjoint .0. z
  disjoint G g
  disjoint G m
  disjoint G n
  disjoint G y
  disjoint G z
  disjoint M f
  disjoint M k
  disjoint M m
  disjoint M n
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint B g
  disjoint B k
  disjoint B m
  disjoint B n
  disjoint B y
  disjoint B z
  disjoint F g
  disjoint F k
  disjoint F m
  disjoint F n
  disjoint F y
  disjoint F z
  disjoint H f
  disjoint H g
  disjoint H k
  disjoint H m
  disjoint H n
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint W g
  disjoint W k
  disjoint W m
  disjoint W n
  disjoint W y
  disjoint W z
  assert |- ( ph -> E! x E. f ( f : ( 1 ... ( # ` W ) ) -1-1-onto-> W /\ x = ( seq 1 ( .+ , ( F o. f ) ) ` ( # ` W ) ) ) )

  proof
    wph
    c1
    cW
    chash
    cfv
    #
    cfz
    co
    #
    cW
    vf
    cv
    #
    wf1o
    #
    vx
    cv
    #
    @0
    c.pl
    cF
    @2
    ccom
    #
    c1
    cseq
    #
    cfv
    #
    wceq
    #
    wa
    #
    vf
    wex
    #
    vx
    wex
    #
    @10
    @1
    cW
    vg
    cv
    #
    wf1o
    #
    vy
    cv
    #
    @0
    c.pl
    cF
    @12
    ccom
    #
    c1
    cseq
    #
    cfv
    #
    wceq
    #
    wa
    #
    vg
    wex
    #
    wa
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    wal
    vx
    wal
    @10
    vx
    weu
    wph
    @3
    vf
    wex
    #
    @11
    wph
    @0
    cn
    wcel
    #
    @24
    wph
    cW
    c0
    wceq
    #
    wn
    @25
    @24
    wa
    #
    wph
    cW
    c0
    gsumval3a.n
    neneqd
    wph
    @26
    @27
    wph
    cW
    cfn
    wcel
    @26
    @27
    wo
    gsumval3a.t
    cW
    vf
    fz1f1o
    syl
    ord
    mpd
    #
    simprd
    @11
    @9
    vx
    wex
    #
    vf
    wex
    @24
    @9
    vx
    vf
    excom
    @29
    @3
    vf
    @29
    @8
    @3
    wa
    vx
    wex
    @3
    @3
    @8
    vx
    exancom
    @3
    @3
    vx
    @7
    @0
    @6
    fvex
    @8
    @3
    biidd
    ceqsexv
    bitri
    exbii
    bitri
    sylibr
    wph
    @23
    vx
    vy
    @21
    @9
    @19
    wa
    #
    vg
    wex
    vf
    wex
    wph
    @22
    @9
    @19
    vf
    vg
    eeanv
    wph
    @30
    @22
    vf
    vg
    @30
    @3
    @13
    wa
    #
    @8
    @18
    wa
    #
    wa
    wph
    @22
    @3
    @13
    @8
    @18
    an4
    wph
    @31
    @32
    @22
    wph
    @31
    wa
    #
    @22
    @32
    @7
    @17
    wceq
    @33
    vx
    vy
    vz
    cF
    crn
    #
    c.pl
    cB
    vk
    @12
    ccnv
    #
    @2
    ccom
    #
    @15
    @5
    c1
    @0
    @33
    cG
    cmnd
    wcel
    #
    @4
    cB
    wcel
    #
    @14
    cB
    wcel
    #
    wa
    @4
    @14
    c.pl
    co
    #
    cB
    wcel
    #
    wph
    @37
    @31
    gsumval3.g
    adantr
    #
    @37
    @38
    @39
    @41
    cB
    c.pl
    cG
    @4
    @14
    gsumval3.b
    gsumval3.p
    mndcl
    3expb
    sylan
    @33
    @4
    @34
    wcel
    #
    @14
    @34
    wcel
    #
    wa
    wa
    @4
    @34
    cZ
    cfv
    #
    wcel
    #
    @44
    @40
    @14
    @4
    c.pl
    co
    wceq
    @33
    @43
    @46
    @44
    @33
    @34
    @45
    @4
    wph
    @34
    @45
    wss
    @31
    gsumval3.c
    adantr
    sselda
    adantrr
    @33
    @43
    @44
    simprr
    c.pl
    @34
    cG
    @4
    @14
    cZ
    gsumval3.p
    gsumval3.z
    cntzi
    syl2anc
    @33
    @37
    @38
    @39
    vz
    cv
    #
    cB
    wcel
    w3a
    @40
    @47
    c.pl
    co
    @4
    @14
    @47
    c.pl
    co
    c.pl
    co
    wceq
    @42
    cB
    c.pl
    cG
    @4
    @14
    @47
    gsumval3.b
    gsumval3.p
    mndass
    sylan
    @33
    @0
    cn
    c1
    cuz
    cfv
    wph
    @25
    @31
    wph
    @25
    @24
    @28
    simpld
    adantr
    nnuz
    syl6eleq
    @33
    cA
    cB
    cF
    wf
    #
    @34
    cB
    wss
    wph
    @48
    @31
    gsumval3.f
    adantr
    #
    cA
    cB
    cF
    frn
    syl
    @33
    cW
    @1
    @35
    wf1o
    #
    @3
    @1
    @1
    @36
    wf1o
    #
    @33
    @13
    @50
    wph
    @3
    @13
    simprr
    #
    @1
    cW
    @12
    f1ocnv
    syl
    wph
    @3
    @13
    simprl
    #
    @1
    cW
    @1
    @35
    @2
    f1oco
    syl2anc
    #
    @33
    @4
    @1
    wcel
    #
    wa
    #
    @4
    @15
    cfv
    #
    @4
    @12
    cfv
    #
    cF
    cfv
    #
    @34
    @33
    @1
    cW
    @12
    wf
    #
    @55
    @57
    @59
    wceq
    @33
    @13
    @60
    @52
    @1
    cW
    @12
    f1of
    syl
    #
    @1
    cW
    @4
    cF
    @12
    fvco3
    sylan
    @56
    cF
    cA
    wfn
    #
    @58
    cA
    wcel
    @59
    @34
    wcel
    @33
    @62
    @55
    @33
    @48
    @62
    @49
    cA
    cB
    cF
    ffn
    syl
    adantr
    @33
    @1
    cA
    @4
    @12
    @33
    @1
    cW
    cA
    @12
    @61
    wph
    cW
    cA
    wss
    @31
    gsumval3a.s
    adantr
    fssd
    #
    ffvelrnda
    cA
    @58
    cF
    fnfvelrn
    syl2anc
    eqeltrd
    @33
    vk
    cv
    #
    @1
    wcel
    #
    wa
    #
    @64
    @2
    cfv
    #
    cF
    cfv
    #
    @64
    @36
    cfv
    #
    @12
    cfv
    #
    cF
    cfv
    #
    @64
    @5
    cfv
    #
    @69
    @15
    cfv
    #
    @66
    @67
    @70
    cF
    @66
    @70
    @67
    @35
    cfv
    #
    @12
    cfv
    #
    @67
    @66
    @69
    @74
    @12
    @33
    @1
    cW
    @2
    wf
    #
    @65
    @69
    @74
    wceq
    @33
    @3
    @76
    @53
    @1
    cW
    @2
    f1of
    syl
    #
    @1
    cW
    @64
    @35
    @2
    fvco3
    sylan
    fveq2d
    @66
    @13
    @67
    cW
    wcel
    @75
    @67
    wceq
    @33
    @13
    @65
    @52
    adantr
    @33
    @1
    cW
    @64
    @2
    @77
    ffvelrnda
    @1
    cW
    @67
    @12
    f1ocnvfv2
    syl2anc
    eqtr2d
    fveq2d
    @33
    @76
    @65
    @72
    @68
    wceq
    @77
    @1
    cW
    @64
    cF
    @2
    fvco3
    sylan
    @33
    @65
    @69
    @1
    wcel
    #
    @73
    @71
    wceq
    #
    @33
    @1
    @1
    @64
    @36
    @33
    @51
    @1
    @1
    @36
    wf
    @54
    @1
    @1
    @36
    f1of
    syl
    ffvelrnda
    @33
    @1
    cA
    @12
    wf
    @78
    @79
    @63
    @1
    cA
    @69
    cF
    @12
    fvco3
    sylan
    syldan
    3eqtr4d
    seqf1o
    @4
    @7
    @14
    @17
    eqeq12
    syl5ibrcom
    expimpd
    syl5bir
    exlimdvv
    syl5bir
    alrimivv
    @10
    @20
    vx
    vy
    @22
    @10
    @3
    @14
    @7
    wceq
    #
    wa
    #
    vf
    wex
    @20
    @22
    @9
    @81
    vf
    @22
    @8
    @80
    @3
    @4
    @14
    @7
    eqeq1
    anbi2d
    exbidv
    @81
    @19
    vf
    vg
    vf
    vg
    weq
    #
    @3
    @13
    @80
    @18
    @1
    cW
    @2
    @12
    f1oeq1
    @82
    @7
    @17
    @14
    @82
    @0
    @6
    @16
    @82
    @5
    @15
    c.pl
    c1
    @2
    @12
    cF
    coeq2
    seqeq3d
    fveq1d
    eqeq2d
    anbi12d
    cbvexv
    syl6bb
    eu4
    sylanbrc
end
