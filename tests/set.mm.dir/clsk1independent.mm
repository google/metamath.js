include "c3o.mm"
include "cvv.mm"
include "wcel.mm"
include "c0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wss.mm"
include "cpw.mm"
include "wral.mm"
include "wa.mm"
include "cun.mm"
include "wi.mm"
include "wn.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "wal.mm"
include "con0.mm"
include "3on.mm"
include "elexi.mm"
include "csn.mm"
include "c1o.mm"
include "cpr.mm"
include "cif.mm"
include "cmpt.mm"
include "wf.mm"
include "eqid.mm"
include "wo.mm"
include "notnotr.mm"
include "a1i.mm"
include "c2o.mm"
include "csuc.mm"
include "sssucid.mm"
include "2on.mm"
include "elpw.mm"
include "mpbir.mm"
include "df2o3.mm"
include "df-3o.mm"
include "eqcomi.mm"
include "pweqi.mm"
include "3eltr3i.mm"
include "2a1i.mm"
include "jcad.mm"
include "con1d.mm"
include "anc2ri.mm"
include "orrd.mm"
include "ifel.mm"
include "sylibr.mm"
include "fmpti.mm"
include "pwex.mm"
include "elmap.mm"
include "clsk1indlem0.mm"
include "clsk1indlem2.mm"
include "pm3.2i.mm"
include "clsk1indlem3.mm"
include "clsk1indlem4.mm"
include "clsk1indlem1.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "sseq2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "uneq12d.mm"
include "sseq12d.mm"
include "2ralbidv.mm"
include "id.mm"
include "fveq12d.mm"
include "eqeq12d.mm"
include "rexnal2.mm"
include "pm4.61.mm"
include "notbid.mm"
include "anbi2d.mm"
include "syl5bb.mm"
include "2rexbidv.mm"
include "syl5bbr.mm"
include "rspcev.mm"
include "mp2an.mm"
include "pweq.mm"
include "oveq12d.mm"
include "wb.mm"
include "raleqdv.mm"
include "raleqbidv.mm"
include "rexeqbidv.mm"
include "ralv.mm"
include "xchbinx.mm"
include "sylib.mm"

theorem clsk1independent
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vt: setvar t
  let vk: setvar k
  let vs: setvar s
  let vb: setvar b
  let vr: setvar r
  assume clsnim.k0: |- ( ph <-> ( k ` (/) ) = (/) )
  assume clsnim.k1: |- ( ps <-> A. s e. ~P b A. t e. ~P b ( s C_ t -> ( k ` s ) C_ ( k ` t ) ) )
  assume clsnim.k2: |- ( ch <-> A. s e. ~P b s C_ ( k ` s ) )
  assume clsnim.k3: |- ( th <-> A. s e. ~P b A. t e. ~P b ( k ` ( s u. t ) ) C_ ( ( k ` s ) u. ( k ` t ) ) )
  assume clsnim.k4: |- ( ta <-> A. s e. ~P b ( k ` ( k ` s ) ) = ( k ` s ) )

  disjoint b k
  disjoint b s
  disjoint b t
  disjoint k s
  disjoint k t
  disjoint s t
  disjoint k r
  disjoint r s
  disjoint r t
  assert |- -. A. b A. k e. ( ~P b ^m ~P b ) ( ( ( ph /\ ch ) /\ ( th /\ ta ) ) -> ps )

  proof
    c3o
    cvv
    wcel
    #
    c0
    vk
    cv
    #
    cfv
    #
    c0
    wceq
    #
    vs
    cv
    #
    @4
    @1
    cfv
    #
    wss
    #
    vs
    c3o
    cpw
    #
    wral
    #
    wa
    #
    @4
    vt
    cv
    #
    cun
    #
    @1
    cfv
    #
    @5
    @10
    @1
    cfv
    #
    cun
    #
    wss
    #
    vt
    @7
    wral
    #
    vs
    @7
    wral
    #
    @5
    @1
    cfv
    #
    @5
    wceq
    #
    vs
    @7
    wral
    #
    wa
    #
    wa
    #
    @4
    @10
    wss
    #
    @5
    @13
    wss
    #
    wi
    #
    vt
    @7
    wral
    #
    vs
    @7
    wral
    #
    wn
    #
    wa
    #
    vk
    @7
    @7
    cmap
    co
    #
    wrex
    #
    wph
    wch
    wa
    #
    wth
    wta
    wa
    #
    wa
    #
    wps
    wi
    #
    vk
    vb
    cv
    #
    cpw
    #
    @37
    cmap
    co
    #
    wral
    #
    vb
    wal
    #
    wn
    #
    c3o
    con0
    3on
    elexi
    #
    vr
    @7
    vr
    cv
    #
    c0
    csn
    wceq
    #
    c0
    c1o
    cpr
    #
    @43
    cif
    #
    cmpt
    #
    @30
    wcel
    #
    c0
    @47
    cfv
    #
    c0
    wceq
    #
    @4
    @4
    @47
    cfv
    #
    wss
    #
    vs
    @7
    wral
    #
    wa
    #
    @11
    @47
    cfv
    #
    @51
    @10
    @47
    cfv
    #
    cun
    #
    wss
    #
    vt
    @7
    wral
    vs
    @7
    wral
    #
    @51
    @47
    cfv
    #
    @51
    wceq
    #
    vs
    @7
    wral
    #
    wa
    #
    wa
    #
    @23
    @51
    @56
    wss
    #
    wn
    #
    wa
    #
    vt
    @7
    wrex
    vs
    @7
    wrex
    #
    wa
    #
    @31
    @48
    @7
    @7
    @47
    wf
    vr
    @7
    @7
    @46
    @47
    @47
    eqid
    #
    @43
    @7
    wcel
    #
    @44
    @45
    @7
    wcel
    #
    wa
    #
    @44
    wn
    #
    @71
    wa
    #
    wo
    @46
    @7
    wcel
    @71
    @73
    @75
    @71
    @73
    wn
    @74
    @71
    @74
    @73
    @71
    @74
    wn
    #
    @44
    @72
    @76
    @44
    wi
    @71
    @44
    notnotr
    a1i
    @72
    @71
    @76
    c2o
    c2o
    csuc
    #
    cpw
    #
    @45
    @7
    c2o
    @78
    wcel
    c2o
    @77
    wss
    c2o
    sssucid
    c2o
    @77
    c2o
    con0
    2on
    elexi
    elpw
    mpbir
    df2o3
    @77
    c3o
    c3o
    @77
    df-3o
    eqcomi
    pweqi
    3eltr3i
    2a1i
    jcad
    con1d
    anc2ri
    orrd
    @44
    @45
    @43
    @7
    ifel
    sylibr
    fmpti
    @7
    @7
    @47
    c3o
    @42
    pwex
    #
    @79
    elmap
    mpbir
    @64
    @68
    @54
    @63
    @50
    @53
    @47
    vr
    @70
    clsk1indlem0
    @47
    vs
    vr
    @70
    clsk1indlem2
    pm3.2i
    @59
    @62
    vt
    @47
    vs
    vr
    @70
    clsk1indlem3
    @47
    vs
    vr
    @70
    clsk1indlem4
    pm3.2i
    pm3.2i
    vt
    @47
    vs
    vr
    @70
    clsk1indlem1
    pm3.2i
    @29
    @69
    vk
    @47
    @30
    @1
    @47
    wceq
    #
    @22
    @64
    @28
    @68
    @80
    @9
    @54
    @21
    @63
    @80
    @3
    @50
    @8
    @53
    @80
    @2
    @49
    c0
    c0
    @1
    @47
    fveq1
    eqeq1d
    @80
    @6
    @52
    vs
    @7
    @80
    @5
    @51
    @4
    @4
    @1
    @47
    fveq1
    #
    sseq2d
    ralbidv
    anbi12d
    @80
    @17
    @59
    @20
    @62
    @80
    @15
    @58
    vs
    vt
    @7
    @7
    @80
    @12
    @55
    @14
    @57
    @11
    @1
    @47
    fveq1
    @80
    @5
    @51
    @13
    @56
    @81
    @10
    @1
    @47
    fveq1
    #
    uneq12d
    sseq12d
    2ralbidv
    @80
    @19
    @61
    vs
    @7
    @80
    @18
    @60
    @5
    @51
    @80
    @5
    @51
    @1
    @47
    @80
    id
    @81
    fveq12d
    @81
    eqeq12d
    ralbidv
    anbi12d
    anbi12d
    @28
    @25
    wn
    #
    vt
    @7
    wrex
    vs
    @7
    wrex
    @80
    @68
    @25
    vs
    vt
    @7
    @7
    rexnal2
    @80
    @83
    @67
    vs
    vt
    @7
    @7
    @83
    @23
    @24
    wn
    #
    wa
    @80
    @67
    @23
    @24
    pm4.61
    @80
    @84
    @66
    @23
    @80
    @24
    @65
    @80
    @5
    @51
    @13
    @56
    @81
    @82
    sseq12d
    notbid
    anbi2d
    syl5bb
    2rexbidv
    syl5bbr
    anbi12d
    rspcev
    mp2an
    @0
    @31
    wa
    @35
    wn
    #
    vk
    @38
    wrex
    #
    vb
    cvv
    wrex
    #
    @41
    @86
    @31
    vb
    c3o
    cvv
    @36
    c3o
    wceq
    #
    @85
    @29
    vk
    @38
    @30
    @88
    @37
    @7
    @37
    @7
    cmap
    @36
    c3o
    pweq
    #
    @89
    oveq12d
    @85
    @34
    wps
    wn
    #
    wa
    @88
    @29
    @34
    wps
    pm4.61
    @88
    @34
    @22
    @90
    @28
    @88
    @32
    @9
    @33
    @21
    @88
    wph
    @3
    wch
    @8
    wph
    @3
    wb
    @88
    clsnim.k0
    a1i
    wch
    @6
    vs
    @37
    wral
    @88
    @8
    clsnim.k2
    @88
    @6
    vs
    @37
    @7
    @89
    raleqdv
    syl5bb
    anbi12d
    @88
    wth
    @17
    wta
    @20
    wth
    @15
    vt
    @37
    wral
    #
    vs
    @37
    wral
    @88
    @17
    clsnim.k3
    @88
    @91
    @16
    vs
    @37
    @7
    @89
    @88
    @15
    vt
    @37
    @7
    @89
    raleqdv
    raleqbidv
    syl5bb
    wta
    @19
    vs
    @37
    wral
    @88
    @20
    clsnim.k4
    @88
    @19
    vs
    @37
    @7
    @89
    raleqdv
    syl5bb
    anbi12d
    anbi12d
    @88
    wps
    @27
    wps
    @25
    vt
    @37
    wral
    #
    vs
    @37
    wral
    @88
    @27
    clsnim.k1
    @88
    @92
    @26
    vs
    @37
    @7
    @89
    @88
    @25
    vt
    @37
    @7
    @89
    raleqdv
    raleqbidv
    syl5bb
    notbid
    anbi12d
    syl5bb
    rexeqbidv
    rspcev
    @87
    @39
    vb
    cvv
    wral
    @40
    @35
    vb
    vk
    cvv
    @38
    rexnal2
    @39
    vb
    ralv
    xchbinx
    sylib
    mp2an
end
