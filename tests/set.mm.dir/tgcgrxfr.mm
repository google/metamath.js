include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "wcel.mm"
include "cs3.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "c2.mm"
include "cle.mm"
include "adantr.mm"
include "cstrkg.mm"
include "simpr.mm"
include "tgldim0itv.mm"
include "tgldim0cgr.mm"
include "trgcgr.mm"
include "eleq1.mm"
include "eqidd.mm"
include "id.mm"
include "s3eqd.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "wne.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "axtgsegcon.mm"
include "ad7antr.mm"
include "ad2antrr.mm"
include "simpllr.mm"
include "simpld.mm"
include "simprl.mm"
include "tgbtwnexch3.mm"
include "simp-5r.mm"
include "simprd.mm"
include "necomd.mm"
include "tgbtwnexch.mm"
include "tgbtwncom.mm"
include "simprr.mm"
include "tgcgrextend.mm"
include "eqcomd.mm"
include "tgsegconeq.mm"
include "oveq2d.mm"
include "eleqtrd.mm"
include "eqtr3d.mm"
include "tgcgrcomlr.mm"
include "jca.mm"
include "ad5antr.mm"
include "r19.29a.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "tgbtwndiff.mm"
include "cbs.mm"
include "tgldimor.mm"
include "mpjaodan.mm"

theorem tgcgrxfr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let c.sm: class .~
  let ve: setvar e
  let cF: class F
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let vf: setvar f
  let vg: setvar g
  assume tgcgrxfr.p: |- P = ( Base ` G )
  assume tgcgrxfr.m: |- .- = ( dist ` G )
  assume tgcgrxfr.i: |- I = ( Itv ` G )
  assume tgcgrxfr.r: |- .~ = ( cgrG ` G )
  assume tgcgrxfr.g: |- ( ph -> G e. TarskiG )
  assume tgcgrxfr.a: |- ( ph -> A e. P )
  assume tgcgrxfr.b: |- ( ph -> B e. P )
  assume tgcgrxfr.c: |- ( ph -> C e. P )
  assume tgcgrxfr.d: |- ( ph -> D e. P )
  assume tgcgrxfr.f: |- ( ph -> F e. P )
  assume tgcgrxfr.1: |- ( ph -> B e. ( A I C ) )
  assume tgcgrxfr.2: |- ( ph -> ( A .- C ) = ( D .- F ) )

  disjoint A e
  disjoint B e
  disjoint C e
  disjoint D e
  disjoint F e
  disjoint I e
  disjoint P e
  disjoint .- e
  disjoint .~ e
  disjoint e ph
  disjoint A f
  disjoint A g
  disjoint e f
  disjoint e g
  disjoint f g
  disjoint B f
  disjoint B g
  disjoint C f
  disjoint C g
  disjoint D f
  disjoint D g
  disjoint F f
  disjoint F g
  disjoint I f
  disjoint I g
  disjoint P f
  disjoint P g
  disjoint .- f
  disjoint .- g
  disjoint .~ f
  disjoint .~ g
  disjoint f ph
  disjoint g ph
  assert |- ( ph -> E. e e. P ( e e. ( D I F ) /\ <" A B C "> .~ <" D e F "> ) )

  proof
    wph
    cP
    chash
    cfv
    #
    c1
    wceq
    #
    ve
    cv
    #
    cD
    cF
    cI
    co
    #
    wcel
    #
    cA
    cB
    cC
    cs3
    #
    cD
    @2
    cF
    cs3
    #
    c.sm
    wbr
    #
    wa
    #
    ve
    cP
    wrex
    #
    c2
    @0
    cle
    wbr
    #
    wph
    @1
    wa
    #
    cA
    cP
    wcel
    #
    cA
    @3
    wcel
    #
    @5
    cD
    cA
    cF
    cs3
    #
    c.sm
    wbr
    #
    @9
    wph
    @12
    @1
    tgcgrxfr.a
    adantr
    #
    @11
    cA
    cD
    cF
    cP
    cG
    cI
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    wph
    cG
    cstrkg
    wcel
    #
    @1
    tgcgrxfr.g
    adantr
    #
    @16
    wph
    cD
    cP
    wcel
    #
    @1
    tgcgrxfr.d
    adantr
    #
    wph
    cF
    cP
    wcel
    #
    @1
    tgcgrxfr.f
    adantr
    #
    wph
    @1
    simpr
    #
    tgldim0itv
    @11
    cA
    cB
    cC
    cD
    cP
    c.sm
    cA
    cF
    cG
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.r
    @18
    @16
    wph
    cB
    cP
    wcel
    #
    @1
    tgcgrxfr.b
    adantr
    #
    wph
    cC
    cP
    wcel
    #
    @1
    tgcgrxfr.c
    adantr
    #
    @20
    @16
    @22
    @11
    cA
    cB
    cD
    cA
    cP
    cG
    cI
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    @18
    @16
    @25
    @20
    @23
    @16
    tgldim0cgr
    @11
    cB
    cC
    cA
    cF
    cP
    cG
    cI
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    @18
    @25
    @27
    @16
    @23
    @22
    tgldim0cgr
    @11
    cC
    cA
    cF
    cD
    cP
    cG
    cI
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    @18
    @27
    @16
    @22
    @23
    @20
    tgldim0cgr
    trgcgr
    @8
    @13
    @15
    wa
    ve
    cA
    cP
    @2
    cA
    wceq
    #
    @4
    @13
    @7
    @15
    @2
    cA
    @3
    eleq1
    @28
    @6
    @14
    @5
    c.sm
    @28
    cD
    @2
    cF
    cF
    cD
    cA
    @28
    cD
    eqidd
    @28
    id
    @28
    cF
    eqidd
    s3eqd
    breq2d
    anbi12d
    rspcev
    syl12anc
    wph
    @10
    wa
    #
    cD
    cF
    vg
    cv
    #
    cI
    co
    wcel
    #
    cD
    @30
    wne
    #
    wa
    #
    @9
    vg
    cP
    @29
    @30
    cP
    wcel
    #
    wa
    #
    @33
    wa
    #
    cD
    @30
    @2
    cI
    co
    wcel
    #
    cD
    @2
    c.mi
    co
    #
    cA
    cB
    c.mi
    co
    #
    wceq
    #
    wa
    #
    ve
    cP
    wrex
    @9
    @36
    ve
    cA
    cB
    cP
    cG
    cI
    c.mi
    @30
    cD
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    wph
    @17
    @10
    @34
    @33
    tgcgrxfr.g
    ad3antrrr
    #
    @29
    @34
    @33
    simplr
    #
    wph
    @19
    @10
    @34
    @33
    tgcgrxfr.d
    ad3antrrr
    wph
    @12
    @10
    @34
    @33
    tgcgrxfr.a
    ad3antrrr
    wph
    @24
    @10
    @34
    @33
    tgcgrxfr.b
    ad3antrrr
    #
    axtgsegcon
    @36
    @41
    @8
    ve
    cP
    @36
    @2
    cP
    wcel
    #
    wa
    #
    @41
    @8
    @46
    @41
    wa
    #
    @2
    @30
    vf
    cv
    #
    cI
    co
    wcel
    #
    @2
    @48
    c.mi
    co
    #
    cB
    cC
    c.mi
    co
    #
    wceq
    #
    wa
    #
    @8
    vf
    cP
    @47
    @48
    cP
    wcel
    #
    wa
    #
    @53
    wa
    #
    @4
    @7
    @56
    @2
    cD
    @48
    cI
    co
    @3
    @56
    @30
    cD
    @2
    @48
    cP
    cG
    cI
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    wph
    @17
    @10
    @34
    @33
    @45
    @41
    @54
    @53
    tgcgrxfr.g
    ad7antr
    #
    @47
    @34
    @54
    @53
    @36
    @34
    @45
    @41
    @43
    ad2antrr
    #
    ad2antrr
    #
    wph
    @19
    @10
    @34
    @33
    @45
    @41
    @54
    @53
    tgcgrxfr.d
    ad7antr
    #
    @47
    @45
    @54
    @53
    @36
    @45
    @41
    simplr
    #
    ad2antrr
    #
    @47
    @54
    @53
    simplr
    #
    @56
    @37
    @40
    @46
    @41
    @54
    @53
    simpllr
    #
    simpld
    #
    @55
    @49
    @52
    simprl
    #
    tgbtwnexch3
    #
    @56
    @48
    cF
    cD
    cI
    @56
    cD
    cA
    cC
    @30
    cP
    @48
    cF
    cG
    cI
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    @57
    @60
    wph
    @12
    @10
    @34
    @33
    @45
    @41
    @54
    @53
    tgcgrxfr.a
    ad7antr
    #
    wph
    @26
    @10
    @34
    @33
    @45
    @41
    @54
    @53
    tgcgrxfr.c
    ad7antr
    #
    @59
    @63
    wph
    @21
    @10
    @34
    @33
    @45
    @41
    @54
    @53
    tgcgrxfr.f
    ad7antr
    #
    @56
    cD
    @30
    @56
    @31
    @32
    @35
    @33
    @45
    @41
    @54
    @53
    simp-5r
    #
    simprd
    necomd
    @56
    @30
    cD
    @2
    @48
    cP
    cG
    cI
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    @57
    @59
    @60
    @62
    @63
    @65
    @66
    tgbtwnexch
    @56
    cF
    cD
    @30
    cP
    cG
    cI
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    @57
    @70
    @60
    @59
    @56
    @31
    @32
    @71
    simpld
    tgbtwncom
    @56
    cD
    @2
    @48
    cA
    cP
    cB
    cC
    cG
    cI
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    @57
    @60
    @62
    @63
    @68
    wph
    @24
    @10
    @34
    @33
    @45
    @41
    @54
    @53
    tgcgrxfr.b
    ad7antr
    #
    @69
    @67
    wph
    cB
    cA
    cC
    cI
    co
    wcel
    @10
    @34
    @33
    @45
    @41
    @54
    @53
    tgcgrxfr.1
    ad7antr
    @56
    @37
    @40
    @64
    simprd
    #
    @55
    @49
    @52
    simprr
    #
    tgcgrextend
    @56
    cA
    cC
    c.mi
    co
    #
    cD
    cF
    c.mi
    co
    #
    wph
    @75
    @76
    wceq
    @10
    @34
    @33
    @45
    @41
    @54
    @53
    tgcgrxfr.2
    ad7antr
    eqcomd
    tgsegconeq
    #
    oveq2d
    eleqtrd
    @56
    cA
    cB
    cC
    cD
    cP
    c.sm
    @2
    cF
    cG
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.r
    @57
    @68
    @72
    @69
    @60
    @62
    @70
    @56
    @38
    @39
    @73
    eqcomd
    @56
    @50
    @51
    @2
    cF
    c.mi
    co
    @74
    @56
    @48
    cF
    @2
    c.mi
    @77
    oveq2d
    eqtr3d
    wph
    cC
    cA
    c.mi
    co
    cF
    cD
    c.mi
    co
    wceq
    @10
    @34
    @33
    @45
    @41
    @54
    @53
    wph
    cA
    cC
    cD
    cF
    cP
    cG
    cI
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    tgcgrxfr.g
    tgcgrxfr.a
    tgcgrxfr.c
    tgcgrxfr.d
    tgcgrxfr.f
    tgcgrxfr.2
    tgcgrcomlr
    ad7antr
    trgcgr
    jca
    @47
    vf
    cB
    cC
    cP
    cG
    cI
    c.mi
    @30
    @2
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    @36
    @17
    @45
    @41
    @42
    ad2antrr
    @58
    @61
    @36
    @24
    @45
    @41
    @44
    ad2antrr
    wph
    @26
    @10
    @34
    @33
    @45
    @41
    tgcgrxfr.c
    ad5antr
    axtgsegcon
    r19.29a
    ex
    reximdva
    mpd
    @29
    cF
    cD
    cP
    cG
    cI
    c.mi
    vg
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    wph
    @17
    @10
    tgcgrxfr.g
    adantr
    wph
    @21
    @10
    tgcgrxfr.f
    adantr
    wph
    @19
    @10
    tgcgrxfr.d
    adantr
    wph
    @10
    simpr
    tgbtwndiff
    r19.29a
    wph
    cA
    cP
    cbs
    cG
    tgcgrxfr.p
    tgcgrxfr.a
    tgldimor
    mpjaodan
end
