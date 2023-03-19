include "wcel.mm"
include "wral.mm"
include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "cco1.mm"
include "cfv.mm"
include "wceq.mm"
include "cfn.mm"
include "wi.mm"
include "cv.mm"
include "wa.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "raleq.mm"
include "anbi2d.mm"
include "mpteq1.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "c0g.mm"
include "cn0.mm"
include "cxp.mm"
include "mpt0.mm"
include "oveq2i.mm"
include "eqid.mm"
include "gsum0.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "a1i.mm"
include "crg.mm"
include "coe1z.mm"
include "syl.mm"
include "cvv.mm"
include "fvex.mm"
include "fvconst2g.mm"
include "sylancr.mm"
include "3eqtrd.mm"
include "syl6eqr.mm"
include "adantr.mm"
include "wn.mm"
include "coe1fzgsumdlem.mm"
include "3expia.mm"
include "a2d.mm"
include "impexp.mm"
include "3imtr4g.mm"
include "findcard2s.mm"
include "expd.mm"
include "mpcom.mm"
include "mpd.mm"

theorem coe1fzgsumd
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cP: class P
  let cR: class R
  let cK: class K
  let cM: class M
  let cN: class N
  let va: setvar a
  let vm: setvar m
  let vn: setvar n
  assume coe1fzgsumd.p: |- P = ( Poly1 ` R )
  assume coe1fzgsumd.b: |- B = ( Base ` P )
  assume coe1fzgsumd.r: |- ( ph -> R e. Ring )
  assume coe1fzgsumd.k: |- ( ph -> K e. NN0 )
  assume coe1fzgsumd.m: |- ( ph -> A. x e. N M e. B )
  assume coe1fzgsumd.n: |- ( ph -> N e. Fin )

  disjoint B x
  disjoint K x
  disjoint N x
  disjoint B a
  disjoint B m
  disjoint B n
  disjoint a m
  disjoint a n
  disjoint m n
  disjoint K a
  disjoint K m
  disjoint K n
  disjoint N n
  disjoint n x
  disjoint N m
  disjoint m x
  disjoint N a
  disjoint a x
  disjoint M a
  disjoint M m
  disjoint M n
  disjoint P a
  disjoint P m
  disjoint P n
  disjoint R a
  disjoint R m
  disjoint R n
  disjoint a ph
  disjoint m ph
  disjoint n ph
  assert |- ( ph -> ( ( coe1 ` ( P gsum ( x e. N |-> M ) ) ) ` K ) = ( R gsum ( x e. N |-> ( ( coe1 ` M ) ` K ) ) ) )

  proof
    wph
    cM
    cB
    wcel
    #
    vx
    cN
    wral
    #
    cK
    cP
    vx
    cN
    cM
    cmpt
    #
    cgsu
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cR
    vx
    cN
    cK
    cM
    cco1
    cfv
    cfv
    #
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    coe1fzgsumd.m
    cN
    cfn
    wcel
    #
    wph
    @1
    @9
    wi
    coe1fzgsumd.n
    @10
    wph
    @1
    @9
    wph
    @0
    vx
    vn
    cv
    #
    wral
    #
    wa
    #
    cK
    cP
    vx
    @11
    cM
    cmpt
    #
    cgsu
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cR
    vx
    @11
    @6
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    wi
    wph
    @0
    vx
    c0
    wral
    #
    wa
    #
    cK
    cP
    vx
    c0
    cM
    cmpt
    #
    cgsu
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cR
    vx
    c0
    @6
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    wi
    wph
    @0
    vx
    vm
    cv
    #
    wral
    #
    wa
    #
    cK
    cP
    vx
    @30
    cM
    cmpt
    #
    cgsu
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cR
    vx
    @30
    @6
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    wi
    #
    wph
    @0
    vx
    @30
    va
    cv
    #
    csn
    cun
    #
    wral
    #
    wa
    #
    cK
    cP
    vx
    @42
    cM
    cmpt
    #
    cgsu
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cR
    vx
    @42
    @6
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    wi
    #
    wph
    @1
    wa
    #
    @9
    wi
    vn
    vm
    va
    cN
    @11
    c0
    wceq
    #
    @13
    @22
    @20
    @29
    @54
    @12
    @21
    wph
    @0
    vx
    @11
    c0
    raleq
    anbi2d
    @54
    @17
    @26
    @19
    @28
    @54
    cK
    @16
    @25
    @54
    @15
    @24
    cco1
    @54
    @14
    @23
    cP
    cgsu
    vx
    @11
    c0
    cM
    mpteq1
    oveq2d
    fveq2d
    fveq1d
    @54
    @18
    @27
    cR
    cgsu
    vx
    @11
    c0
    @6
    mpteq1
    oveq2d
    eqeq12d
    imbi12d
    @11
    @30
    wceq
    #
    @13
    @32
    @20
    @39
    @55
    @12
    @31
    wph
    @0
    vx
    @11
    @30
    raleq
    anbi2d
    @55
    @17
    @36
    @19
    @38
    @55
    cK
    @16
    @35
    @55
    @15
    @34
    cco1
    @55
    @14
    @33
    cP
    cgsu
    vx
    @11
    @30
    cM
    mpteq1
    oveq2d
    fveq2d
    fveq1d
    @55
    @18
    @37
    cR
    cgsu
    vx
    @11
    @30
    @6
    mpteq1
    oveq2d
    eqeq12d
    imbi12d
    @11
    @42
    wceq
    #
    @13
    @44
    @20
    @51
    @56
    @12
    @43
    wph
    @0
    vx
    @11
    @42
    raleq
    anbi2d
    @56
    @17
    @48
    @19
    @50
    @56
    cK
    @16
    @47
    @56
    @15
    @46
    cco1
    @56
    @14
    @45
    cP
    cgsu
    vx
    @11
    @42
    cM
    mpteq1
    oveq2d
    fveq2d
    fveq1d
    @56
    @18
    @49
    cR
    cgsu
    vx
    @11
    @42
    @6
    mpteq1
    oveq2d
    eqeq12d
    imbi12d
    @11
    cN
    wceq
    #
    @13
    @53
    @20
    @9
    @57
    @12
    @1
    wph
    @0
    vx
    @11
    cN
    raleq
    anbi2d
    @57
    @17
    @5
    @19
    @8
    @57
    cK
    @16
    @4
    @57
    @15
    @3
    cco1
    @57
    @14
    @2
    cP
    cgsu
    vx
    @11
    cN
    cM
    mpteq1
    oveq2d
    fveq2d
    fveq1d
    @57
    @18
    @7
    cR
    cgsu
    vx
    @11
    cN
    @6
    mpteq1
    oveq2d
    eqeq12d
    imbi12d
    wph
    @29
    @21
    wph
    @26
    cR
    c0g
    cfv
    #
    @28
    wph
    @26
    cK
    cP
    c0g
    cfv
    #
    cco1
    cfv
    #
    cfv
    cK
    cn0
    @58
    csn
    cxp
    #
    cfv
    #
    @58
    wph
    cK
    @25
    @60
    @25
    @60
    wceq
    wph
    @24
    @59
    cco1
    @24
    cP
    c0
    cgsu
    co
    @59
    @23
    c0
    cP
    cgsu
    vx
    cM
    mpt0
    oveq2i
    cP
    @59
    @59
    eqid
    #
    gsum0
    eqtri
    fveq2i
    a1i
    fveq1d
    wph
    cK
    @60
    @61
    wph
    cR
    crg
    wcel
    @60
    @61
    wceq
    coe1fzgsumd.r
    cP
    cR
    @58
    @59
    coe1fzgsumd.p
    @63
    @58
    eqid
    #
    coe1z
    syl
    fveq1d
    wph
    @58
    cvv
    wcel
    cK
    cn0
    wcel
    @62
    @58
    wceq
    cR
    c0g
    fvex
    coe1fzgsumd.k
    cn0
    @58
    cK
    cvv
    fvconst2g
    sylancr
    3eqtrd
    @28
    cR
    c0
    cgsu
    co
    @58
    @27
    c0
    cR
    cgsu
    vx
    @6
    mpt0
    oveq2i
    cR
    @58
    @64
    gsum0
    eqtri
    syl6eqr
    adantr
    @30
    cfn
    wcel
    #
    @41
    @30
    wcel
    wn
    #
    wa
    #
    wph
    @31
    @39
    wi
    #
    wi
    wph
    @43
    @51
    wi
    #
    wi
    @40
    @52
    @67
    wph
    @68
    @69
    @65
    @66
    wph
    @68
    @69
    wi
    wph
    vx
    cB
    cP
    cR
    vm
    cK
    cM
    va
    coe1fzgsumd.p
    coe1fzgsumd.b
    coe1fzgsumd.r
    coe1fzgsumd.k
    coe1fzgsumdlem
    3expia
    a2d
    wph
    @31
    @39
    impexp
    wph
    @43
    @51
    impexp
    3imtr4g
    findcard2s
    expd
    mpcom
    mpd
end
