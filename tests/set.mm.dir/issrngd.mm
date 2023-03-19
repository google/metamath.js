include "cstf.mm"
include "cfv.mm"
include "coppr.mm"
include "crh.mm"
include "co.mm"
include "wcel.mm"
include "ccnv.mm"
include "wceq.mm"
include "csr.mm"
include "cbs.mm"
include "cplusg.mm"
include "cmulr.mm"
include "cur.mm"
include "eqid.mm"
include "oppr1.mm"
include "crg.mm"
include "opprring.mm"
include "syl.mm"
include "cstv.mm"
include "cv.mm"
include "wral.mm"
include "ringidcl.mm"
include "wa.mm"
include "ex.mm"
include "eleq2d.mm"
include "fveq1d.mm"
include "fveq12d.mm"
include "eqeq1d.mm"
include "3imtr3d.mm"
include "imp.mm"
include "eqcomd.mm"
include "ralrimiva.mm"
include "id.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "oveq1d.mm"
include "eleq12d.mm"
include "ralrimiv.mm"
include "eleq1d.mm"
include "3expib.mm"
include "anbi12d.mm"
include "oveqd.mm"
include "oveq123d.mm"
include "ralrimivv.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "eqtr4d.mm"
include "ringlidm.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"
include "stafval.mm"
include "3eqtr4d.mm"
include "opprmul.mm"
include "syl6eqr.mm"
include "ringcl.mm"
include "3expb.mm"
include "sylan.mm"
include "oveqan12d.mm"
include "adantl.mm"
include "opprbas.mm"
include "oppradd.mm"
include "staffval.mm"
include "fmptd.mm"
include "ringacl.mm"
include "isrhmd.mm"
include "cmpt.mm"
include "wf1o.mm"
include "wf.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "rspccva.mm"
include "adantrl.mm"
include "eqeq2d.mm"
include "syl5ibrcom.mm"
include "adantrr.mm"
include "impbid.mm"
include "f1ocnv2d.mm"
include "simprd.mm"
include "syl6reqr.mm"
include "issrng.mm"
include "sylanbrc.mm"

theorem issrngd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let c.as: class .*
  let cK: class K
  assume issrngd.k: |- ( ph -> K = ( Base ` R ) )
  assume issrngd.p: |- ( ph -> .+ = ( +g ` R ) )
  assume issrngd.t: |- ( ph -> .x. = ( .r ` R ) )
  assume issrngd.c: |- ( ph -> .* = ( *r ` R ) )
  assume issrngd.r: |- ( ph -> R e. Ring )
  assume issrngd.cl: |- ( ( ph /\ x e. K ) -> ( .* ` x ) e. K )
  assume issrngd.dp: |- ( ( ph /\ x e. K /\ y e. K ) -> ( .* ` ( x .+ y ) ) = ( ( .* ` x ) .+ ( .* ` y ) ) )
  assume issrngd.dt: |- ( ( ph /\ x e. K /\ y e. K ) -> ( .* ` ( x .x. y ) ) = ( ( .* ` y ) .x. ( .* ` x ) ) )
  assume issrngd.id: |- ( ( ph /\ x e. K ) -> ( .* ` ( .* ` x ) ) = x )

  disjoint x y
  disjoint K x
  disjoint K y
  disjoint R x
  disjoint R y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> R e. *Ring )

  proof
    wph
    cR
    cstf
    cfv
    #
    cR
    cR
    coppr
    cfv
    #
    crh
    co
    wcel
    @0
    @0
    ccnv
    #
    wceq
    cR
    csr
    wcel
    wph
    vx
    vy
    cR
    cbs
    cfv
    #
    @3
    cR
    cplusg
    cfv
    #
    @4
    cR
    @1
    cR
    cmulr
    cfv
    #
    @1
    cmulr
    cfv
    #
    cR
    cur
    cfv
    #
    @0
    @7
    @3
    eqid
    #
    @7
    eqid
    #
    cR
    @7
    @1
    @1
    eqid
    #
    @9
    oppr1
    @5
    eqid
    #
    @6
    eqid
    #
    issrngd.r
    wph
    cR
    crg
    wcel
    #
    @1
    crg
    wcel
    issrngd.r
    cR
    @1
    @10
    opprring
    syl
    wph
    @7
    cR
    cstv
    cfv
    #
    cfv
    #
    @15
    @14
    cfv
    #
    @7
    @0
    cfv
    #
    @7
    wph
    @7
    @15
    @5
    co
    #
    @18
    @14
    cfv
    #
    @15
    @16
    wph
    @18
    @16
    @15
    @5
    co
    #
    @19
    wph
    @7
    @16
    @15
    @5
    wph
    @7
    @3
    wcel
    #
    vx
    cv
    #
    @22
    @14
    cfv
    #
    @14
    cfv
    #
    wceq
    #
    vx
    @3
    wral
    #
    @7
    @16
    wceq
    #
    wph
    @13
    @21
    issrngd.r
    @3
    cR
    @7
    @8
    @9
    ringidcl
    syl
    #
    wph
    @25
    vx
    @3
    wph
    @22
    @3
    wcel
    #
    wa
    @24
    @22
    wph
    @29
    @24
    @22
    wceq
    #
    wph
    @22
    cK
    wcel
    #
    @22
    c.as
    cfv
    #
    c.as
    cfv
    #
    @22
    wceq
    #
    @29
    @30
    wph
    @31
    @34
    issrngd.id
    ex
    wph
    cK
    @3
    @22
    issrngd.k
    eleq2d
    #
    wph
    @33
    @24
    @22
    wph
    @32
    @23
    c.as
    @14
    issrngd.c
    wph
    @22
    c.as
    @14
    issrngd.c
    fveq1d
    #
    fveq12d
    eqeq1d
    3imtr3d
    imp
    eqcomd
    #
    ralrimiva
    #
    @25
    @27
    vx
    @7
    @3
    @22
    @7
    wceq
    #
    @22
    @7
    @24
    @16
    @39
    id
    @39
    @23
    @15
    @14
    @22
    @7
    @14
    fveq2
    #
    fveq2d
    eqeq12d
    rspcv
    sylc
    #
    oveq1d
    wph
    @21
    @15
    @3
    wcel
    #
    @22
    vy
    cv
    #
    @5
    co
    #
    @14
    cfv
    #
    @43
    @14
    cfv
    #
    @23
    @5
    co
    #
    wceq
    #
    vy
    @3
    wral
    vx
    @3
    wral
    @19
    @20
    wceq
    #
    @28
    wph
    @21
    @23
    @3
    wcel
    #
    vx
    @3
    wral
    @42
    @28
    wph
    @50
    vx
    @3
    wph
    @31
    @32
    cK
    wcel
    #
    @29
    @50
    wph
    @31
    @51
    issrngd.cl
    ex
    @35
    wph
    @32
    @23
    cK
    @3
    @36
    issrngd.k
    eleq12d
    3imtr3d
    #
    ralrimiv
    @50
    @42
    vx
    @7
    @3
    @39
    @23
    @15
    @3
    @40
    eleq1d
    rspcv
    sylc
    #
    wph
    @48
    vx
    vy
    @3
    @3
    wph
    @31
    @43
    cK
    wcel
    #
    wa
    #
    @22
    @43
    c.x
    co
    #
    c.as
    cfv
    #
    @43
    c.as
    cfv
    #
    @32
    c.x
    co
    #
    wceq
    #
    @29
    @43
    @3
    wcel
    #
    wa
    #
    @48
    wph
    @31
    @54
    @60
    issrngd.dt
    3expib
    wph
    @31
    @29
    @54
    @61
    @35
    wph
    cK
    @3
    @43
    issrngd.k
    eleq2d
    anbi12d
    #
    wph
    @57
    @45
    @59
    @47
    wph
    @56
    @44
    c.as
    @14
    issrngd.c
    wph
    c.x
    @5
    @22
    @43
    issrngd.t
    oveqd
    fveq12d
    wph
    @58
    @46
    @32
    @23
    c.x
    @5
    issrngd.t
    wph
    @43
    c.as
    @14
    issrngd.c
    fveq1d
    #
    @36
    oveq123d
    eqeq12d
    3imtr3d
    #
    ralrimivv
    @48
    @49
    @7
    @43
    @5
    co
    #
    @14
    cfv
    #
    @46
    @15
    @5
    co
    #
    wceq
    vx
    vy
    @7
    @15
    @3
    @3
    @39
    @45
    @67
    @47
    @68
    @39
    @44
    @66
    @14
    @22
    @7
    @43
    @5
    oveq1
    fveq2d
    @39
    @23
    @15
    @46
    @5
    @40
    oveq2d
    eqeq12d
    @43
    @15
    wceq
    #
    @67
    @19
    @68
    @20
    @69
    @66
    @18
    @14
    @43
    @15
    @7
    @5
    oveq2
    fveq2d
    @69
    @46
    @16
    @15
    @5
    @43
    @15
    @14
    fveq2
    oveq1d
    eqeq12d
    rspc2va
    syl21anc
    eqtr4d
    wph
    @13
    @42
    @18
    @15
    wceq
    issrngd.r
    @53
    @3
    cR
    @5
    @7
    @15
    @8
    @11
    @9
    ringlidm
    syl2anc
    #
    wph
    @18
    @15
    @14
    @70
    fveq2d
    3eqtr3d
    wph
    @21
    @17
    @15
    wceq
    @28
    @7
    @3
    cR
    @0
    @14
    @8
    @14
    eqid
    #
    @0
    eqid
    #
    stafval
    syl
    @41
    3eqtr4d
    wph
    @62
    wa
    #
    @45
    @23
    @46
    @6
    co
    #
    @44
    @0
    cfv
    #
    @22
    @0
    cfv
    #
    @43
    @0
    cfv
    #
    @6
    co
    #
    @73
    @45
    @47
    @74
    wph
    @62
    @48
    @65
    imp
    @3
    cR
    @6
    @5
    @1
    @23
    @46
    @8
    @11
    @10
    @12
    opprmul
    syl6eqr
    @73
    @44
    @3
    wcel
    #
    @75
    @45
    wceq
    wph
    @13
    @62
    @79
    issrngd.r
    @13
    @29
    @61
    @79
    @3
    cR
    @5
    @22
    @43
    @8
    @11
    ringcl
    3expb
    sylan
    @44
    @3
    cR
    @0
    @14
    @8
    @71
    @72
    stafval
    syl
    @62
    @78
    @74
    wceq
    wph
    @29
    @61
    @76
    @23
    @77
    @46
    @6
    @22
    @3
    cR
    @0
    @14
    @8
    @71
    @72
    stafval
    #
    @43
    @3
    cR
    @0
    @14
    @8
    @71
    @72
    stafval
    #
    oveqan12d
    adantl
    3eqtr4d
    @3
    cR
    @1
    @10
    @8
    opprbas
    @4
    eqid
    #
    @4
    cR
    @1
    @10
    @82
    oppradd
    wph
    vx
    @3
    @23
    @3
    @0
    wph
    @29
    @50
    @52
    imp
    #
    vx
    @3
    cR
    @0
    @14
    @8
    @71
    @72
    staffval
    #
    fmptd
    #
    @73
    @22
    @43
    @4
    co
    #
    @14
    cfv
    #
    @23
    @46
    @4
    co
    #
    @86
    @0
    cfv
    #
    @76
    @77
    @4
    co
    #
    wph
    @62
    @87
    @88
    wceq
    #
    wph
    @55
    @22
    @43
    c.pl
    co
    #
    c.as
    cfv
    #
    @32
    @58
    c.pl
    co
    #
    wceq
    #
    @62
    @91
    wph
    @31
    @54
    @95
    issrngd.dp
    3expib
    @63
    wph
    @93
    @87
    @94
    @88
    wph
    @92
    @86
    c.as
    @14
    issrngd.c
    wph
    c.pl
    @4
    @22
    @43
    issrngd.p
    oveqd
    fveq12d
    wph
    @32
    @23
    @58
    @46
    c.pl
    @4
    issrngd.p
    @36
    @64
    oveq123d
    eqeq12d
    3imtr3d
    imp
    @73
    @86
    @3
    wcel
    #
    @89
    @87
    wceq
    wph
    @13
    @62
    @96
    issrngd.r
    @13
    @29
    @61
    @96
    @3
    @4
    cR
    @22
    @43
    @8
    @82
    ringacl
    3expb
    sylan
    @86
    @3
    cR
    @0
    @14
    @8
    @71
    @72
    stafval
    syl
    @62
    @90
    @88
    wceq
    wph
    @29
    @61
    @76
    @23
    @77
    @46
    @4
    @80
    @81
    oveqan12d
    adantl
    3eqtr4d
    isrhmd
    wph
    @2
    vy
    @3
    @46
    cmpt
    #
    @0
    wph
    @3
    @3
    @0
    wf1o
    @2
    @97
    wceq
    wph
    vx
    vy
    @3
    @3
    @23
    @46
    @0
    @84
    @83
    wph
    @46
    @3
    wcel
    #
    vy
    @3
    wph
    @3
    @3
    @0
    wf
    @98
    vy
    @3
    wral
    @85
    vy
    @3
    @3
    @46
    @0
    vy
    @3
    cR
    @0
    @14
    @8
    @71
    @72
    staffval
    #
    fmpt
    sylibr
    r19.21bi
    @73
    @22
    @46
    wceq
    #
    @43
    @23
    wceq
    #
    @73
    @101
    @100
    @43
    @46
    @14
    cfv
    #
    wceq
    #
    wph
    @61
    @103
    @29
    wph
    @26
    @61
    @103
    @38
    @25
    @103
    vx
    @43
    @3
    @22
    @43
    wceq
    #
    @22
    @43
    @24
    @102
    @104
    id
    @104
    @23
    @46
    @14
    @22
    @43
    @14
    fveq2
    fveq2d
    eqeq12d
    rspccva
    sylan
    adantrl
    @100
    @23
    @102
    @43
    @22
    @46
    @14
    fveq2
    eqeq2d
    syl5ibrcom
    @73
    @100
    @101
    @25
    wph
    @29
    @25
    @61
    @37
    adantrr
    @101
    @46
    @24
    @22
    @43
    @23
    @14
    fveq2
    eqeq2d
    syl5ibrcom
    impbid
    f1ocnv2d
    simprd
    @99
    syl6reqr
    cR
    @0
    @1
    @10
    @72
    issrng
    sylanbrc
end
