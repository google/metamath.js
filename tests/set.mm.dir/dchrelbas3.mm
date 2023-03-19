include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "ccnfld.mm"
include "cmhm.mm"
include "co.mm"
include "cv.mm"
include "cc0.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "cc.mm"
include "wf.mm"
include "cmulr.mm"
include "cmul.mm"
include "wceq.mm"
include "cur.mm"
include "c1.mm"
include "w3a.mm"
include "dchrelbas2.mm"
include "wb.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "cmnd.mm"
include "crg.mm"
include "ccrg.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "zncrng.mm"
include "syl.mm"
include "crngring.mm"
include "eqid.mm"
include "ringmgp.mm"
include "cnring.mm"
include "ax-mp.mm"
include "mgpbas.mm"
include "cnfldbas.mm"
include "mgpplusg.mm"
include "cnfldmul.mm"
include "ringidval.mm"
include "cnfld1.mm"
include "ismhm.mm"
include "baib.mm"
include "sylancl.mm"
include "adantr.mm"
include "wal.mm"
include "biimt.mm"
include "adantl.mm"
include "wn.mm"
include "ad3antrrr.mm"
include "simprl.mm"
include "simprr.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "simpllr.mm"
include "rspcv.mm"
include "sylc.mm"
include "unitmulclb.mm"
include "sylibd.mm"
include "necon1bd.mm"
include "imp.mm"
include "wo.mm"
include "anim12d.mm"
include "con3dimp.mm"
include "neanior.mm"
include "con2bii.mm"
include "sylibr.mm"
include "simplr.mm"
include "ffvelrnd.mm"
include "mul0ord.mm"
include "mpbird.mm"
include "eqtr4d.mm"
include "a1d.mm"
include "2thd.mm"
include "pm2.61dan.mm"
include "pm5.74da.mm"
include "unitcl.mm"
include "anim12i.mm"
include "pm4.71ri.mm"
include "imbi1i.mm"
include "impexp.mm"
include "bitri.mm"
include "syl6bbr.mm"
include "2albidv.mm"
include "r2al.mm"
include "3bitr4g.mm"
include "adantrr.mm"
include "pm5.32da.mm"
include "3anan32.mm"
include "an31.mm"
include "bitrd.mm"
include "sylan2br.mm"
include "ancom.mm"
include "df-3an.mm"
include "anbi2i.mm"
include "an13.mm"

theorem dchrelbas3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cD: class D
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  let cZ: class Z
  let cA: class A
  let vk: setvar k
  let vz: setvar z
  let vb: setvar b
  let vn: setvar n
  let cC: class C
  let cE: class E
  let cY: class Y
  assume dchrval.g: |- G = ( DChr ` N )
  assume dchrval.z: |- Z = ( Z/nZ ` N )
  assume dchrval.b: |- B = ( Base ` Z )
  assume dchrval.u: |- U = ( Unit ` Z )
  assume dchrval.n: |- ( ph -> N e. NN )
  assume dchrbas.b: |- D = ( Base ` G )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint N x
  disjoint U x
  disjoint U y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint Z x
  disjoint Z y
  disjoint A k
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint B k
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint b n
  disjoint b z
  disjoint D b
  disjoint n z
  disjoint D n
  disjoint D z
  disjoint b x
  disjoint N b
  disjoint n x
  disjoint N n
  disjoint N z
  disjoint U k
  disjoint U z
  disjoint C k
  disjoint E k
  disjoint b k
  disjoint b y
  disjoint b ph
  disjoint k n
  disjoint k ph
  disjoint n y
  disjoint n ph
  disjoint ph z
  disjoint X z
  disjoint Z k
  disjoint Z z
  disjoint Y k
  assert |- ( ph -> ( X e. D <-> ( X : B --> CC /\ ( A. x e. U A. y e. U ( X ` ( x ( .r ` Z ) y ) ) = ( ( X ` x ) x. ( X ` y ) ) /\ ( X ` ( 1r ` Z ) ) = 1 /\ A. x e. B ( ( X ` x ) =/= 0 -> x e. U ) ) ) ) )

  proof
    wph
    cX
    cD
    wcel
    cX
    cZ
    cmgp
    cfv
    #
    ccnfld
    cmgp
    cfv
    #
    cmhm
    co
    wcel
    #
    vx
    cv
    #
    cX
    cfv
    #
    cc0
    wne
    #
    @3
    cU
    wcel
    #
    wi
    #
    vx
    cB
    wral
    #
    wa
    #
    cB
    cc
    cX
    wf
    #
    @3
    vy
    cv
    #
    cZ
    cmulr
    cfv
    #
    co
    #
    cX
    cfv
    #
    @4
    @11
    cX
    cfv
    #
    cmul
    co
    #
    wceq
    #
    vy
    cU
    wral
    vx
    cU
    wral
    #
    cZ
    cur
    cfv
    #
    cX
    cfv
    c1
    wceq
    #
    @8
    w3a
    #
    wa
    #
    wph
    vx
    cB
    cD
    cU
    cG
    cN
    cX
    cZ
    dchrval.g
    dchrval.z
    dchrval.b
    dchrval.u
    dchrval.n
    dchrbas.b
    dchrelbas2
    wph
    @8
    @2
    wa
    @8
    @18
    @20
    wa
    #
    @10
    wa
    #
    wa
    #
    @9
    @22
    wph
    @8
    @2
    @24
    @8
    wph
    vz
    cv
    #
    cX
    cfv
    #
    cc0
    wne
    #
    @26
    cU
    wcel
    #
    wi
    #
    vz
    cB
    wral
    #
    @2
    @24
    wb
    @30
    @7
    vz
    vx
    cB
    @26
    @3
    wceq
    #
    @28
    @5
    @29
    @6
    @32
    @27
    @4
    cc0
    @26
    @3
    cX
    fveq2
    neeq1d
    @26
    @3
    cU
    eleq1
    imbi12d
    #
    cbvralv
    wph
    @31
    wa
    #
    @2
    @10
    @17
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @20
    w3a
    #
    @24
    wph
    @2
    @36
    wb
    #
    @31
    wph
    @0
    cmnd
    wcel
    #
    @1
    cmnd
    wcel
    #
    @37
    wph
    cZ
    crg
    wcel
    #
    @38
    wph
    cZ
    ccrg
    wcel
    #
    @40
    wph
    cN
    cn0
    wcel
    @41
    wph
    cN
    dchrval.n
    nnnn0d
    cN
    cZ
    dchrval.z
    zncrng
    syl
    #
    cZ
    crngring
    syl
    #
    cZ
    @0
    @0
    eqid
    #
    ringmgp
    syl
    ccnfld
    crg
    wcel
    @39
    cnring
    ccnfld
    @1
    @1
    eqid
    #
    ringmgp
    ax-mp
    @2
    @38
    @39
    wa
    @36
    vx
    vy
    cB
    cc
    @12
    cmul
    @0
    @1
    cX
    c1
    @19
    cB
    cZ
    @0
    @44
    dchrval.b
    mgpbas
    cc
    ccnfld
    @1
    @45
    cnfldbas
    mgpbas
    cZ
    @12
    @0
    @44
    @12
    eqid
    #
    mgpplusg
    ccnfld
    cmul
    @1
    @45
    cnfldmul
    mgpplusg
    cZ
    @19
    @0
    @44
    @19
    eqid
    ringidval
    ccnfld
    c1
    @1
    @45
    cnfld1
    ringidval
    ismhm
    baib
    sylancl
    adantr
    @34
    @10
    @20
    wa
    #
    @35
    wa
    @47
    @18
    wa
    @36
    @24
    @34
    @47
    @35
    @18
    @34
    @10
    @35
    @18
    wb
    @20
    @34
    @10
    wa
    #
    @3
    cB
    wcel
    #
    @11
    cB
    wcel
    #
    wa
    #
    @17
    wi
    #
    vy
    wal
    vx
    wal
    @6
    @11
    cU
    wcel
    #
    wa
    #
    @17
    wi
    #
    vy
    wal
    vx
    wal
    @35
    @18
    @48
    @52
    @55
    vx
    vy
    @48
    @52
    @51
    @55
    wi
    #
    @55
    @48
    @51
    @17
    @55
    @48
    @51
    wa
    #
    @54
    @17
    @55
    wb
    #
    @54
    @58
    @57
    @54
    @17
    biimt
    adantl
    @57
    @54
    wn
    #
    wa
    #
    @17
    @55
    @60
    @14
    cc0
    @16
    @57
    @59
    @14
    cc0
    wceq
    @57
    @54
    @14
    cc0
    @57
    @14
    cc0
    wne
    #
    @13
    cU
    wcel
    #
    @54
    @57
    @13
    cB
    wcel
    #
    @31
    @61
    @62
    wi
    #
    @57
    @40
    @49
    @50
    @63
    wph
    @40
    @31
    @10
    @51
    @43
    ad3antrrr
    @48
    @49
    @50
    simprl
    #
    @48
    @49
    @50
    simprr
    #
    cB
    cZ
    @12
    @3
    @11
    dchrval.b
    @46
    ringcl
    syl3anc
    wph
    @31
    @10
    @51
    simpllr
    #
    @30
    @64
    vz
    @13
    cB
    @26
    @13
    wceq
    #
    @28
    @61
    @29
    @62
    @68
    @27
    @14
    cc0
    @26
    @13
    cX
    fveq2
    neeq1d
    @26
    @13
    cU
    eleq1
    imbi12d
    rspcv
    sylc
    @57
    @41
    @49
    @50
    @62
    @54
    wb
    wph
    @41
    @31
    @10
    @51
    @42
    ad3antrrr
    @65
    @66
    cB
    cZ
    @12
    cU
    @3
    @11
    dchrval.u
    @46
    dchrval.b
    unitmulclb
    syl3anc
    sylibd
    necon1bd
    imp
    @60
    @16
    cc0
    wceq
    #
    @4
    cc0
    wceq
    @15
    cc0
    wceq
    wo
    #
    @60
    @5
    @15
    cc0
    wne
    #
    wa
    #
    wn
    @70
    @57
    @72
    @54
    @57
    @5
    @6
    @71
    @53
    @57
    @49
    @31
    @7
    @65
    @67
    @30
    @7
    vz
    @3
    cB
    @33
    rspcv
    sylc
    @57
    @50
    @31
    @71
    @53
    wi
    #
    @66
    @67
    @30
    @73
    vz
    @11
    cB
    @26
    @11
    wceq
    #
    @28
    @71
    @29
    @53
    @74
    @27
    @15
    cc0
    @26
    @11
    cX
    fveq2
    neeq1d
    @26
    @11
    cU
    eleq1
    imbi12d
    rspcv
    sylc
    anim12d
    con3dimp
    @72
    @70
    @4
    cc0
    @15
    cc0
    neanior
    con2bii
    sylibr
    @57
    @69
    @70
    wb
    @59
    @57
    @4
    @15
    @57
    cB
    cc
    @3
    cX
    @34
    @10
    @51
    simplr
    #
    @65
    ffvelrnd
    @57
    cB
    cc
    @11
    cX
    @75
    @66
    ffvelrnd
    mul0ord
    adantr
    mpbird
    eqtr4d
    #
    @60
    @17
    @54
    @76
    a1d
    2thd
    pm2.61dan
    pm5.74da
    @55
    @51
    @54
    wa
    #
    @17
    wi
    @56
    @54
    @77
    @17
    @54
    @51
    @6
    @49
    @53
    @50
    cB
    cZ
    cU
    @3
    dchrval.b
    dchrval.u
    unitcl
    cB
    cZ
    cU
    @11
    dchrval.b
    dchrval.u
    unitcl
    anim12i
    pm4.71ri
    imbi1i
    @51
    @54
    @17
    impexp
    bitri
    syl6bbr
    2albidv
    @17
    vx
    vy
    cB
    cB
    r2al
    @17
    vx
    vy
    cU
    cU
    r2al
    3bitr4g
    adantrr
    pm5.32da
    @10
    @35
    @20
    3anan32
    @18
    @20
    @10
    an31
    3bitr4g
    bitrd
    sylan2br
    pm5.32da
    @2
    @8
    ancom
    @22
    @10
    @23
    @8
    wa
    #
    wa
    @25
    @21
    @78
    @10
    @18
    @20
    @8
    df-3an
    anbi2i
    @10
    @23
    @8
    an13
    bitri
    3bitr4g
    bitrd
end
