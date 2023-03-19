include "co.mm"
include "wbr.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "legov.mm"
include "cs3.mm"
include "ccgrg.mm"
include "cfv.mm"
include "clng.mm"
include "eqid.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simprl.mm"
include "btwncolg1.mm"
include "simprr.mm"
include "eqcomd.mm"
include "lnext.mm"
include "simpr.mm"
include "simpllr.mm"
include "simpld.mm"
include "tgbtwnxfr.mm"
include "trgcgrcom.mm"
include "cgr3simp3.mm"
include "tgcgrcomlr.mm"
include "jca.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "adantllr.mm"
include "eleq1.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "sylib.mm"
include "r19.29a.mm"
include "btwncolg3.mm"
include "cgr3swap23.mm"
include "eleq2d.mm"
include "eqeq1d.mm"
include "impbida.mm"
include "bitrd.mm"

theorem legov2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let c.le: class .<_
  let c.mi: class .-
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vy: setvar y
  let vz: setvar z
  assume legval.p: |- P = ( Base ` G )
  assume legval.d: |- .- = ( dist ` G )
  assume legval.i: |- I = ( Itv ` G )
  assume legval.l: |- .<_ = ( leG ` G )
  assume legval.g: |- ( ph -> G e. TarskiG )
  assume legov.a: |- ( ph -> A e. P )
  assume legov.b: |- ( ph -> B e. P )
  assume legov.c: |- ( ph -> C e. P )
  assume legov.d: |- ( ph -> D e. P )

  disjoint .- x
  disjoint A x
  disjoint B x
  disjoint C x
  disjoint D x
  disjoint I x
  disjoint P x
  disjoint G x
  disjoint ph x
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint .- c
  disjoint d e
  disjoint d f
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint .- d
  disjoint e f
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint .- e
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint .- f
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint .- y
  disjoint .- z
  disjoint A c
  disjoint A d
  disjoint A e
  disjoint A f
  disjoint A y
  disjoint A z
  disjoint B c
  disjoint B d
  disjoint B e
  disjoint B f
  disjoint B y
  disjoint B z
  disjoint C c
  disjoint C d
  disjoint C e
  disjoint C f
  disjoint C y
  disjoint C z
  disjoint D c
  disjoint D d
  disjoint D e
  disjoint D f
  disjoint D y
  disjoint D z
  disjoint I c
  disjoint I d
  disjoint I e
  disjoint I f
  disjoint I y
  disjoint I z
  disjoint P c
  disjoint P d
  disjoint P e
  disjoint P f
  disjoint P y
  disjoint P z
  disjoint G e
  disjoint G f
  disjoint G y
  disjoint G z
  disjoint c ph
  disjoint d ph
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( ( A .- B ) .<_ ( C .- D ) <-> E. x e. P ( B e. ( A I x ) /\ ( A .- x ) = ( C .- D ) ) ) )

  proof
    wph
    cA
    cB
    c.mi
    co
    #
    cC
    cD
    c.mi
    co
    #
    c.le
    wbr
    vy
    cv
    #
    cC
    cD
    cI
    co
    #
    wcel
    #
    @0
    cC
    @2
    c.mi
    co
    #
    wceq
    #
    wa
    #
    vy
    cP
    wrex
    #
    cB
    cA
    vx
    cv
    #
    cI
    co
    #
    wcel
    #
    cA
    @9
    c.mi
    co
    #
    @1
    wceq
    #
    wa
    #
    vx
    cP
    wrex
    #
    wph
    vy
    cA
    cB
    cC
    cD
    cP
    cG
    cI
    c.le
    c.mi
    legval.p
    legval.d
    legval.i
    legval.l
    legval.g
    legov.a
    legov.b
    legov.c
    legov.d
    legov
    wph
    @8
    @15
    wph
    @8
    wa
    #
    vz
    cv
    #
    @3
    wcel
    #
    @0
    cC
    @17
    c.mi
    co
    #
    wceq
    #
    wa
    #
    @15
    vz
    cP
    wph
    @17
    cP
    wcel
    #
    @21
    @15
    @8
    wph
    @22
    wa
    #
    @21
    wa
    #
    cC
    @17
    cD
    cs3
    cA
    cB
    @9
    cs3
    cG
    ccgrg
    cfv
    #
    wbr
    #
    vx
    cP
    wrex
    @15
    @24
    cA
    cB
    cP
    @25
    cG
    cI
    cG
    clng
    cfv
    #
    c.mi
    cC
    @17
    cD
    vx
    legval.p
    @27
    eqid
    #
    legval.i
    wph
    cG
    cstrkg
    wcel
    #
    @22
    @21
    legval.g
    ad2antrr
    #
    wph
    cC
    cP
    wcel
    #
    @22
    @21
    legov.c
    ad2antrr
    #
    wph
    @22
    @21
    simplr
    #
    wph
    cD
    cP
    wcel
    #
    @22
    @21
    legov.d
    ad2antrr
    #
    @25
    eqid
    #
    wph
    cA
    cP
    wcel
    #
    @22
    @21
    legov.a
    ad2antrr
    #
    wph
    cB
    cP
    wcel
    #
    @22
    @21
    legov.b
    ad2antrr
    #
    legval.d
    @24
    cP
    cG
    cI
    @27
    cC
    cD
    @17
    legval.p
    @28
    legval.i
    @30
    @32
    @35
    @33
    @23
    @18
    @20
    simprl
    btwncolg1
    @24
    @0
    @19
    @23
    @18
    @20
    simprr
    eqcomd
    lnext
    @24
    @26
    @14
    vx
    cP
    @24
    @9
    cP
    wcel
    #
    wa
    #
    @26
    @14
    @42
    @26
    wa
    #
    @11
    @13
    @43
    cC
    @17
    cD
    cA
    cP
    @25
    cB
    @9
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @36
    @24
    @29
    @41
    @26
    @30
    ad2antrr
    #
    @24
    @31
    @41
    @26
    @32
    ad2antrr
    #
    @24
    @22
    @41
    @26
    @33
    ad2antrr
    #
    @24
    @34
    @41
    @26
    @35
    ad2antrr
    #
    @24
    @37
    @41
    @26
    @38
    ad2antrr
    #
    @24
    @39
    @41
    @26
    @40
    ad2antrr
    #
    @24
    @41
    @26
    simplr
    #
    @42
    @26
    simpr
    #
    @43
    @18
    @20
    @23
    @21
    @41
    @26
    simpllr
    simpld
    tgbtwnxfr
    @43
    @9
    cA
    cD
    cC
    cP
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @44
    @50
    @48
    @47
    @45
    @43
    cA
    cB
    @9
    cC
    cP
    @25
    @17
    cD
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @36
    @44
    @48
    @49
    @50
    @45
    @46
    @47
    @43
    cC
    @17
    cD
    cA
    cP
    @25
    cB
    @9
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @36
    @44
    @45
    @46
    @47
    @48
    @49
    @50
    @51
    trgcgrcom
    cgr3simp3
    tgcgrcomlr
    jca
    ex
    reximdva
    mpd
    adantllr
    @16
    @8
    @21
    vz
    cP
    wrex
    wph
    @8
    simpr
    @7
    @21
    vy
    vz
    cP
    @2
    @17
    wceq
    #
    @4
    @18
    @6
    @20
    @2
    @17
    @3
    eleq1
    @52
    @5
    @19
    @0
    @2
    @17
    cC
    c.mi
    oveq2
    eqeq2d
    anbi12d
    cbvrexv
    sylib
    r19.29a
    wph
    @15
    wa
    #
    cB
    cA
    @17
    cI
    co
    #
    wcel
    #
    cA
    @17
    c.mi
    co
    #
    @1
    wceq
    #
    wa
    #
    @8
    vz
    cP
    wph
    @22
    @58
    @8
    @15
    @23
    @58
    wa
    #
    cA
    @17
    cB
    cs3
    cC
    cD
    @2
    cs3
    @25
    wbr
    #
    vy
    cP
    wrex
    @8
    @59
    cC
    cD
    cP
    @25
    cG
    cI
    @27
    c.mi
    cA
    @17
    cB
    vy
    legval.p
    @28
    legval.i
    wph
    @29
    @22
    @58
    legval.g
    ad2antrr
    #
    wph
    @37
    @22
    @58
    legov.a
    ad2antrr
    #
    wph
    @22
    @58
    simplr
    #
    wph
    @39
    @22
    @58
    legov.b
    ad2antrr
    #
    @36
    wph
    @31
    @22
    @58
    legov.c
    ad2antrr
    #
    wph
    @34
    @22
    @58
    legov.d
    ad2antrr
    #
    legval.d
    @59
    cP
    cG
    cI
    @27
    cA
    cB
    @17
    legval.p
    @28
    legval.i
    @61
    @62
    @64
    @63
    @23
    @55
    @57
    simprl
    btwncolg3
    @23
    @55
    @57
    simprr
    lnext
    @59
    @60
    @7
    vy
    cP
    @59
    @2
    cP
    wcel
    #
    wa
    #
    @60
    @7
    @68
    @60
    wa
    #
    @4
    @6
    @69
    cA
    cB
    @17
    cC
    cP
    @25
    @2
    cD
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @36
    @59
    @29
    @67
    @60
    @61
    ad2antrr
    #
    @59
    @37
    @67
    @60
    @62
    ad2antrr
    #
    @59
    @39
    @67
    @60
    @64
    ad2antrr
    #
    @59
    @22
    @67
    @60
    @63
    ad2antrr
    #
    @59
    @31
    @67
    @60
    @65
    ad2antrr
    #
    @59
    @67
    @60
    simplr
    #
    @59
    @34
    @67
    @60
    @66
    ad2antrr
    #
    @69
    cA
    @17
    cB
    cC
    cP
    @25
    cD
    @2
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @36
    @70
    @71
    @73
    @72
    @74
    @76
    @75
    @68
    @60
    simpr
    #
    cgr3swap23
    @69
    @55
    @57
    @23
    @58
    @67
    @60
    simpllr
    simpld
    tgbtwnxfr
    @69
    cB
    cA
    @2
    cC
    cP
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @70
    @72
    @71
    @75
    @74
    @69
    cA
    @17
    cB
    cC
    cP
    @25
    cD
    @2
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @36
    @70
    @71
    @73
    @72
    @74
    @76
    @75
    @77
    cgr3simp3
    tgcgrcomlr
    jca
    ex
    reximdva
    mpd
    adantllr
    @53
    @15
    @58
    vz
    cP
    wrex
    wph
    @15
    simpr
    @14
    @58
    vx
    vz
    cP
    @9
    @17
    wceq
    #
    @11
    @55
    @13
    @57
    @78
    @10
    @54
    cB
    @9
    @17
    cA
    cI
    oveq2
    eleq2d
    @78
    @12
    @56
    @1
    @9
    @17
    cA
    c.mi
    oveq2
    eqeq1d
    anbi12d
    cbvrexv
    sylib
    r19.29a
    impbida
    bitrd
end
