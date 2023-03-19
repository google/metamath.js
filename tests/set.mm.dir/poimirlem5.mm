include "cc0.mm"
include "cfv.mm"
include "c1st.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "caddc.mm"
include "cof.mm"
include "cv.mm"
include "c2nd.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "cima.mm"
include "cun.mm"
include "csb.mm"
include "cmin.mm"
include "cvv.mm"
include "wcel.mm"
include "cmpt.mm"
include "wceq.mm"
include "cfzo.mm"
include "cmap.mm"
include "wf1o.mm"
include "cab.mm"
include "fveq2.mm"
include "breq2d.mm"
include "ifbid.mm"
include "csbeq1d.mm"
include "fveq2d.mm"
include "imaeq1d.mm"
include "xpeq1d.mm"
include "uneq12d.mm"
include "oveq12d.mm"
include "csbeq2dv.mm"
include "eqtrd.mm"
include "mpteq2dv.mm"
include "eqeq2d.mm"
include "elrab2.mm"
include "simprbi.mm"
include "syl.mm"
include "wa.mm"
include "breq1.mm"
include "id.mm"
include "ifbieq1d.mm"
include "iftrued.mm"
include "sylan9eqr.mm"
include "c0ex.mm"
include "c0.mm"
include "oveq2.mm"
include "fz10.mm"
include "syl6eq.mm"
include "imaeq2d.mm"
include "oveq1.mm"
include "0p1e1.mm"
include "oveq1d.mm"
include "ima0.mm"
include "xpeq1i.mm"
include "0xp.mm"
include "eqtri.mm"
include "uneq1i.mm"
include "uncom.mm"
include "un0.mm"
include "3eqtri.mm"
include "oveq2d.mm"
include "csbie.mm"
include "wfo.mm"
include "crab.mm"
include "elrabi.mm"
include "eleq2s.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "fvex.mm"
include "f1oeq1.mm"
include "elab.mm"
include "sylib.mm"
include "f1ofo.mm"
include "foima.mm"
include "syl5eq.mm"
include "adantr.mm"
include "cn0.mm"
include "cn.mm"
include "nnm1nn0.mm"
include "0elfz.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "wfn.mm"
include "elmapfn.mm"
include "fnconstg.mm"
include "mp1i.mm"
include "eqidd.mm"
include "fvconst2.mm"
include "adantl.mm"
include "wf.mm"
include "elmapi.mm"
include "ffvelrnda.mm"
include "elfzonn0.mm"
include "nn0cnd.mm"
include "addid1d.mm"
include "offveq.mm"

theorem poimirlem5
  let wph: wff ph
  let vy: setvar y
  let vt: setvar t
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vj: setvar j
  let cF: class F
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vs: setvar s
  let vz: setvar z
  let vi: setvar i
  let vq: setvar q
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let cM: class M
  let cU: class U
  let cV: class V
  let cB: class B
  assume poimir.0: |- ( ph -> N e. NN )
  assume poimirlem22.s: |- S = { t e. ( ( ( ( 0 ..^ K ) ^m ( 1 ... N ) ) X. { f | f : ( 1 ... N ) -1-1-onto-> ( 1 ... N ) } ) X. ( 0 ... N ) ) | F = ( y e. ( 0 ... ( N - 1 ) ) |-> [_ if ( y < ( 2nd ` t ) , y , ( y + 1 ) ) / j ]_ ( ( 1st ` ( 1st ` t ) ) oF + ( ( ( ( 2nd ` ( 1st ` t ) ) " ( 1 ... j ) ) X. { 1 } ) u. ( ( ( 2nd ` ( 1st ` t ) ) " ( ( j + 1 ) ... N ) ) X. { 0 } ) ) ) ) }
  assume poimirlem9.1: |- ( ph -> T e. S )
  assume poimirlem5.2: |- ( ph -> 0 < ( 2nd ` T ) )

  disjoint j t
  disjoint j y
  disjoint S j
  disjoint t y
  disjoint S t
  disjoint S y
  disjoint f j
  disjoint f t
  disjoint f y
  disjoint j t
  disjoint j y
  disjoint t y
  disjoint j ph
  disjoint ph y
  disjoint F j
  disjoint F y
  disjoint N j
  disjoint N y
  disjoint T j
  disjoint T y
  disjoint ph t
  disjoint K f
  disjoint K j
  disjoint K t
  disjoint N f
  disjoint N t
  disjoint T f
  disjoint F f
  disjoint F t
  disjoint T t
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j p
  disjoint j s
  disjoint j z
  disjoint k m
  disjoint k n
  disjoint k p
  disjoint k s
  disjoint k t
  disjoint k y
  disjoint k z
  disjoint S k
  disjoint m n
  disjoint m p
  disjoint m s
  disjoint m t
  disjoint m y
  disjoint m z
  disjoint S m
  disjoint n p
  disjoint n s
  disjoint n t
  disjoint n y
  disjoint n z
  disjoint S n
  disjoint p s
  disjoint p t
  disjoint p y
  disjoint p z
  disjoint S p
  disjoint s t
  disjoint s y
  disjoint s z
  disjoint S s
  disjoint t z
  disjoint y z
  disjoint S z
  disjoint f i
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f p
  disjoint f q
  disjoint f s
  disjoint f u
  disjoint f w
  disjoint f x
  disjoint f z
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i p
  disjoint i q
  disjoint i s
  disjoint i t
  disjoint i u
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j p
  disjoint j q
  disjoint j s
  disjoint j u
  disjoint j w
  disjoint j x
  disjoint j z
  disjoint k m
  disjoint k n
  disjoint k p
  disjoint k q
  disjoint k s
  disjoint k t
  disjoint k u
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m n
  disjoint m p
  disjoint m q
  disjoint m s
  disjoint m t
  disjoint m u
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n p
  disjoint n q
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint p q
  disjoint p s
  disjoint p t
  disjoint p u
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint q s
  disjoint q t
  disjoint q u
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint s t
  disjoint s u
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t z
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint m ph
  disjoint n ph
  disjoint F m
  disjoint F n
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint M y
  disjoint N m
  disjoint N n
  disjoint T m
  disjoint T n
  disjoint U j
  disjoint U m
  disjoint U n
  disjoint U y
  disjoint V j
  disjoint V m
  disjoint V n
  disjoint V y
  disjoint i ph
  disjoint k ph
  disjoint p ph
  disjoint ph s
  disjoint B f
  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B n
  disjoint B s
  disjoint B t
  disjoint K i
  disjoint K k
  disjoint K n
  disjoint K p
  disjoint K s
  disjoint M f
  disjoint M i
  disjoint M k
  disjoint M p
  disjoint M s
  disjoint M t
  disjoint N i
  disjoint N k
  disjoint N p
  disjoint N s
  disjoint T i
  disjoint T p
  disjoint U f
  disjoint U i
  disjoint U p
  disjoint ph z
  disjoint F k
  disjoint F p
  disjoint F s
  disjoint F z
  disjoint K z
  disjoint N z
  disjoint T k
  disjoint T s
  disjoint T z
  disjoint U k
  disjoint U t
  assert |- ( ph -> ( F ` 0 ) = ( 1st ` ( 1st ` T ) ) )

  proof
    wph
    cc0
    cF
    cfv
    cT
    c1st
    cfv
    #
    c1st
    cfv
    #
    c1
    cN
    cfz
    co
    #
    cc0
    csn
    #
    cxp
    #
    caddc
    cof
    #
    co
    #
    @1
    wph
    vy
    cc0
    vj
    vy
    cv
    #
    cT
    c2nd
    cfv
    #
    clt
    wbr
    #
    @7
    @7
    c1
    caddc
    co
    #
    cif
    #
    @1
    @0
    c2nd
    cfv
    #
    c1
    vj
    cv
    #
    cfz
    co
    #
    cima
    #
    c1
    csn
    #
    cxp
    #
    @12
    @13
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    cima
    #
    @3
    cxp
    #
    cun
    #
    @5
    co
    #
    csb
    #
    @6
    cc0
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    cF
    cvv
    wph
    cT
    cS
    wcel
    #
    cF
    vy
    @26
    @24
    cmpt
    #
    wceq
    #
    poimirlem9.1
    @27
    cT
    cc0
    cK
    cfzo
    co
    #
    @2
    cmap
    co
    #
    @2
    @2
    vf
    cv
    #
    wf1o
    #
    vf
    cab
    #
    cxp
    #
    cc0
    cN
    cfz
    co
    #
    cxp
    #
    wcel
    #
    @29
    cF
    vy
    @26
    vj
    @7
    vt
    cv
    #
    c2nd
    cfv
    #
    clt
    wbr
    #
    @7
    @10
    cif
    #
    @39
    c1st
    cfv
    #
    c1st
    cfv
    #
    @43
    c2nd
    cfv
    #
    @14
    cima
    #
    @16
    cxp
    #
    @45
    @19
    cima
    #
    @3
    cxp
    #
    cun
    #
    @5
    co
    #
    csb
    #
    cmpt
    #
    wceq
    #
    @29
    vt
    cT
    @37
    cS
    @39
    cT
    wceq
    #
    @53
    @28
    cF
    @55
    vy
    @26
    @52
    @24
    @55
    @52
    vj
    @11
    @51
    csb
    @24
    @55
    vj
    @42
    @11
    @51
    @55
    @41
    @9
    @7
    @10
    @55
    @40
    @8
    @7
    clt
    @39
    cT
    c2nd
    fveq2
    breq2d
    ifbid
    csbeq1d
    @55
    vj
    @11
    @51
    @23
    @55
    @44
    @1
    @50
    @22
    @5
    @55
    @43
    @0
    c1st
    @39
    cT
    c1st
    fveq2
    #
    fveq2d
    @55
    @47
    @17
    @49
    @21
    @55
    @46
    @15
    @16
    @55
    @45
    @12
    @14
    @55
    @43
    @0
    c2nd
    @56
    fveq2d
    #
    imaeq1d
    xpeq1d
    @55
    @48
    @20
    @3
    @55
    @45
    @12
    @19
    @57
    imaeq1d
    xpeq1d
    uneq12d
    oveq12d
    csbeq2dv
    eqtrd
    mpteq2dv
    eqeq2d
    poimirlem22.s
    elrab2
    simprbi
    syl
    wph
    @7
    cc0
    wceq
    #
    wa
    #
    @24
    vj
    cc0
    @23
    csb
    #
    @6
    @59
    vj
    @11
    cc0
    @23
    @58
    wph
    @11
    cc0
    @8
    clt
    wbr
    #
    cc0
    @10
    cif
    cc0
    @58
    @9
    @61
    @7
    cc0
    @10
    @7
    cc0
    @8
    clt
    breq1
    @58
    id
    ifbieq1d
    wph
    @61
    cc0
    @10
    poimirlem5.2
    iftrued
    sylan9eqr
    csbeq1d
    wph
    @60
    @6
    wceq
    @58
    wph
    @60
    @1
    @12
    @2
    cima
    #
    @3
    cxp
    #
    @5
    co
    #
    @6
    vj
    cc0
    @23
    @64
    c0ex
    @13
    cc0
    wceq
    #
    @22
    @63
    @1
    @5
    @65
    @22
    @12
    c0
    cima
    #
    @16
    cxp
    #
    @63
    cun
    #
    @63
    @65
    @17
    @67
    @21
    @63
    @65
    @15
    @66
    @16
    @65
    @14
    c0
    @12
    @65
    @14
    c1
    cc0
    cfz
    co
    c0
    @13
    cc0
    c1
    cfz
    oveq2
    fz10
    syl6eq
    imaeq2d
    xpeq1d
    @65
    @20
    @62
    @3
    @65
    @19
    @2
    @12
    @65
    @18
    c1
    cN
    cfz
    @65
    @18
    cc0
    c1
    caddc
    co
    c1
    @13
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    oveq1d
    imaeq2d
    xpeq1d
    uneq12d
    @68
    c0
    @63
    cun
    @63
    c0
    cun
    @63
    @67
    c0
    @63
    @67
    c0
    @16
    cxp
    c0
    @66
    c0
    @16
    @12
    ima0
    xpeq1i
    @16
    0xp
    eqtri
    uneq1i
    c0
    @63
    uncom
    @63
    un0
    3eqtri
    syl6eq
    oveq2d
    csbie
    wph
    @63
    @4
    @1
    @5
    wph
    @62
    @2
    @3
    wph
    @2
    @2
    @12
    wfo
    #
    @62
    @2
    wceq
    wph
    @2
    @2
    @12
    wf1o
    #
    @69
    wph
    @12
    @34
    wcel
    #
    @70
    wph
    @0
    @35
    wcel
    #
    @71
    wph
    @38
    @72
    wph
    @27
    @38
    poimirlem9.1
    @38
    cT
    @54
    vt
    @37
    crab
    cS
    @54
    vt
    cT
    @37
    elrabi
    poimirlem22.s
    eleq2s
    syl
    cT
    @35
    @36
    xp1st
    syl
    #
    @0
    @31
    @34
    xp2nd
    syl
    @33
    @70
    vf
    @12
    @0
    c2nd
    fvex
    @2
    @2
    @32
    @12
    f1oeq1
    elab
    sylib
    @2
    @2
    @12
    f1ofo
    syl
    @2
    @2
    @12
    foima
    syl
    xpeq1d
    oveq2d
    syl5eq
    adantr
    eqtrd
    wph
    @25
    cn0
    wcel
    #
    cc0
    @26
    wcel
    wph
    cN
    cn
    wcel
    @74
    poimir.0
    cN
    nnm1nn0
    syl
    @25
    0elfz
    syl
    wph
    @1
    @4
    @5
    ovexd
    fvmptd
    wph
    vn
    @2
    vn
    cv
    #
    @1
    cfv
    #
    cc0
    caddc
    @1
    @4
    @1
    cvv
    wph
    c1
    cN
    cfz
    ovexd
    wph
    @1
    @31
    wcel
    #
    @1
    @2
    wfn
    wph
    @72
    @77
    @73
    @0
    @31
    @34
    xp1st
    syl
    #
    @1
    @30
    @2
    elmapfn
    syl
    #
    cc0
    cvv
    wcel
    @4
    @2
    wfn
    wph
    c0ex
    @2
    cc0
    cvv
    fnconstg
    mp1i
    @79
    wph
    @75
    @2
    wcel
    #
    wa
    #
    @76
    eqidd
    @80
    @75
    @4
    cfv
    cc0
    wceq
    wph
    @2
    cc0
    @75
    c0ex
    fvconst2
    adantl
    @81
    @76
    @81
    @76
    @81
    @76
    @30
    wcel
    @76
    cn0
    wcel
    wph
    @2
    @30
    @75
    @1
    wph
    @77
    @2
    @30
    @1
    wf
    @78
    @1
    @30
    @2
    elmapi
    syl
    ffvelrnda
    @76
    cK
    elfzonn0
    syl
    nn0cnd
    addid1d
    offveq
    eqtrd
end
