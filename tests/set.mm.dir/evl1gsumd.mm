include "wcel.mm"
include "wral.mm"
include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
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
include "cascl.mm"
include "mpt0.mm"
include "oveq2i.mm"
include "eqid.mm"
include "gsum0.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "crg.mm"
include "ccrg.mm"
include "crngring.mm"
include "syl.mm"
include "ply1scl0.mm"
include "eqcomd.mm"
include "syl5eq.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "grpidcl.mm"
include "evl1scad.mm"
include "simprd.mm"
include "eqtrd.mm"
include "syl6eqr.mm"
include "adantr.mm"
include "wn.mm"
include "evl1gsumdlem.mm"
include "3expia.mm"
include "a2d.mm"
include "impexp.mm"
include "3imtr4g.mm"
include "findcard2s.mm"
include "expd.mm"
include "mpcom.mm"
include "mpd.mm"

theorem evl1gsumd
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cP: class P
  let cR: class R
  let cU: class U
  let cM: class M
  let cN: class N
  let cO: class O
  let cY: class Y
  let vy: setvar y
  let va: setvar a
  let vm: setvar m
  let vn: setvar n
  assume evl1gsumd.q: |- O = ( eval1 ` R )
  assume evl1gsumd.p: |- P = ( Poly1 ` R )
  assume evl1gsumd.b: |- B = ( Base ` R )
  assume evl1gsumd.u: |- U = ( Base ` P )
  assume evl1gsumd.r: |- ( ph -> R e. CRing )
  assume evl1gsumd.y: |- ( ph -> Y e. B )
  assume evl1gsumd.m: |- ( ph -> A. x e. N M e. U )
  assume evl1gsumd.n: |- ( ph -> N e. Fin )

  disjoint O x
  disjoint U x
  disjoint Y x
  disjoint B x
  disjoint N x
  disjoint R x
  disjoint ph x
  disjoint R y
  disjoint ph y
  disjoint M a
  disjoint M m
  disjoint M n
  disjoint a m
  disjoint a n
  disjoint m n
  disjoint N a
  disjoint N m
  disjoint N n
  disjoint a x
  disjoint m x
  disjoint n x
  disjoint O a
  disjoint O m
  disjoint O n
  disjoint P a
  disjoint P m
  disjoint P n
  disjoint R a
  disjoint R m
  disjoint R n
  disjoint U a
  disjoint U m
  disjoint U n
  disjoint Y a
  disjoint Y m
  disjoint Y n
  disjoint a ph
  disjoint m ph
  disjoint n ph
  assert |- ( ph -> ( ( O ` ( P gsum ( x e. N |-> M ) ) ) ` Y ) = ( R gsum ( x e. N |-> ( ( O ` M ) ` Y ) ) ) )

  proof
    wph
    cM
    cU
    wcel
    #
    vx
    cN
    wral
    #
    cY
    cP
    vx
    cN
    cM
    cmpt
    #
    cgsu
    co
    #
    cO
    cfv
    #
    cfv
    #
    cR
    vx
    cN
    cY
    cM
    cO
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
    evl1gsumd.m
    cN
    cfn
    wcel
    #
    wph
    @1
    @9
    wi
    evl1gsumd.n
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
    cY
    cP
    vx
    @11
    cM
    cmpt
    #
    cgsu
    co
    #
    cO
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
    cY
    cP
    vx
    c0
    cM
    cmpt
    #
    cgsu
    co
    #
    cO
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
    cY
    cP
    vx
    @30
    cM
    cmpt
    #
    cgsu
    co
    #
    cO
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
    cY
    cP
    vx
    @42
    cM
    cmpt
    #
    cgsu
    co
    #
    cO
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
    cY
    @16
    @25
    @54
    @15
    @24
    cO
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
    cY
    @16
    @35
    @55
    @15
    @34
    cO
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
    cY
    @16
    @47
    @56
    @15
    @46
    cO
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
    cY
    @16
    @4
    @57
    @15
    @3
    cO
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
    cY
    @58
    cP
    cascl
    cfv
    #
    cfv
    #
    cO
    cfv
    #
    cfv
    #
    @58
    wph
    cY
    @25
    @61
    wph
    @25
    cP
    c0g
    cfv
    #
    cO
    cfv
    @61
    @24
    @63
    cO
    @24
    cP
    c0
    cgsu
    co
    @63
    @23
    c0
    cP
    cgsu
    vx
    cM
    mpt0
    oveq2i
    cP
    @63
    @63
    eqid
    #
    gsum0
    eqtri
    fveq2i
    wph
    @63
    @60
    cO
    wph
    @60
    @63
    wph
    cR
    crg
    wcel
    #
    @60
    @63
    wceq
    wph
    cR
    ccrg
    wcel
    @65
    evl1gsumd.r
    cR
    crngring
    syl
    #
    @59
    cP
    cR
    @63
    @58
    evl1gsumd.p
    @59
    eqid
    #
    @58
    eqid
    #
    @64
    ply1scl0
    syl
    eqcomd
    fveq2d
    syl5eq
    fveq1d
    wph
    @60
    cU
    wcel
    @62
    @58
    wceq
    wph
    @59
    cB
    cP
    cR
    cU
    cO
    @58
    cY
    evl1gsumd.q
    evl1gsumd.p
    evl1gsumd.b
    @67
    evl1gsumd.u
    evl1gsumd.r
    wph
    cR
    cgrp
    wcel
    #
    @58
    cB
    wcel
    wph
    @65
    @69
    @66
    cR
    ringgrp
    syl
    cB
    cR
    @58
    evl1gsumd.b
    @68
    grpidcl
    syl
    evl1gsumd.y
    evl1scad
    simprd
    eqtrd
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
    @68
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
    @72
    wph
    @73
    @74
    @70
    @71
    wph
    @73
    @74
    wi
    wph
    vx
    cB
    cP
    cR
    cU
    vm
    cM
    cO
    cY
    va
    evl1gsumd.q
    evl1gsumd.p
    evl1gsumd.b
    evl1gsumd.u
    evl1gsumd.r
    evl1gsumd.y
    evl1gsumdlem
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
