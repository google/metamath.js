include "cca.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "wa.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "cexp.mm"
include "cz.mm"
include "iscmet3lem3.mm"
include "sylan.mm"
include "r19.2uz.mm"
include "syl.mm"
include "wi.mm"
include "cfz.mm"
include "simpl.mm"
include "adantl.mm"
include "syl6eleq.mm"
include "eluzfz2.mm"
include "ad2antrr.mm"
include "rsp.mm"
include "sylc.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "rspcv.mm"
include "simprr.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "uztrn2.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "raleqbidv.mm"
include "eluzelz.mm"
include "eleq2s.mm"
include "ad2antrl.mm"
include "oveq1.mm"
include "breq1d.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "cr.mm"
include "cme.mm"
include "wf.mm"
include "adantr.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "metcl.mm"
include "syl3anc.mm"
include "1rp.mm"
include "rphalfcl.mm"
include "ax-mp.mm"
include "rpexpcl.mm"
include "sylancr.mm"
include "rpred.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "lttr.mm"
include "mpand.mm"
include "anassrs.mm"
include "ralrimdva.mm"
include "reximdva.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "cxmt.mm"
include "metxmet.mm"
include "eqidd.mm"
include "iscauf.mm"
include "mpbird.mm"

theorem iscmet3lem1
  let wph: wff ph
  let vv: setvar v
  let vu: setvar u
  let cD: class D
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cJ: class J
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let cR: class R
  assume iscmet3.1: |- Z = ( ZZ>= ` M )
  assume iscmet3.2: |- J = ( MetOpen ` D )
  assume iscmet3.3: |- ( ph -> M e. ZZ )
  assume iscmet3.4: |- ( ph -> D e. ( Met ` X ) )
  assume iscmet3.6: |- ( ph -> F : Z --> X )
  assume iscmet3.9: |- ( ph -> A. k e. ZZ A. u e. ( S ` k ) A. v e. ( S ` k ) ( u D v ) < ( ( 1 / 2 ) ^ k ) )
  assume iscmet3.10: |- ( ph -> A. k e. Z A. n e. ( M ... k ) ( F ` k ) e. ( S ` n ) )

  disjoint k n
  disjoint k u
  disjoint k v
  disjoint D k
  disjoint n u
  disjoint n v
  disjoint D n
  disjoint u v
  disjoint D u
  disjoint D v
  disjoint F k
  disjoint F n
  disjoint F u
  disjoint F v
  disjoint X k
  disjoint X n
  disjoint J k
  disjoint J n
  disjoint S k
  disjoint S n
  disjoint S u
  disjoint S v
  disjoint Z k
  disjoint Z n
  disjoint M k
  disjoint M n
  disjoint k ph
  disjoint n ph
  disjoint f g
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f n
  disjoint f r
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint D f
  disjoint g i
  disjoint g j
  disjoint g k
  disjoint g n
  disjoint g r
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint D g
  disjoint i j
  disjoint i k
  disjoint i n
  disjoint i r
  disjoint i s
  disjoint i t
  disjoint i u
  disjoint i v
  disjoint i x
  disjoint i y
  disjoint D i
  disjoint j k
  disjoint j n
  disjoint j r
  disjoint j s
  disjoint j t
  disjoint j u
  disjoint j v
  disjoint j x
  disjoint j y
  disjoint D j
  disjoint k r
  disjoint k s
  disjoint k t
  disjoint k x
  disjoint k y
  disjoint n r
  disjoint n s
  disjoint n t
  disjoint n x
  disjoint n y
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r x
  disjoint r y
  disjoint D r
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint D s
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint D t
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint x y
  disjoint D x
  disjoint D y
  disjoint G j
  disjoint G k
  disjoint G r
  disjoint G x
  disjoint G y
  disjoint R j
  disjoint R k
  disjoint F j
  disjoint F r
  disjoint F x
  disjoint F y
  disjoint X f
  disjoint X g
  disjoint X i
  disjoint X j
  disjoint X r
  disjoint X s
  disjoint X x
  disjoint X y
  disjoint J f
  disjoint J g
  disjoint J i
  disjoint J j
  disjoint J r
  disjoint J s
  disjoint J x
  disjoint J y
  disjoint S y
  disjoint Z f
  disjoint Z g
  disjoint Z i
  disjoint Z j
  disjoint Z r
  disjoint Z s
  disjoint Z y
  disjoint M f
  disjoint M i
  disjoint M j
  disjoint M x
  disjoint f ph
  disjoint g ph
  disjoint i ph
  disjoint j ph
  disjoint ph r
  disjoint ph s
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> F e. ( Cau ` D ) )

  proof
    wph
    cF
    cD
    cca
    cfv
    wcel
    vk
    cv
    #
    cF
    cfv
    #
    vj
    cv
    #
    cF
    cfv
    #
    cD
    co
    #
    vr
    cv
    #
    clt
    wbr
    #
    vj
    @0
    cuz
    cfv
    #
    wral
    #
    vk
    cZ
    wrex
    #
    vr
    crp
    wral
    wph
    @9
    vr
    crp
    wph
    @5
    crp
    wcel
    #
    wa
    #
    c1
    c2
    cdiv
    co
    #
    @0
    cexp
    co
    #
    @5
    clt
    wbr
    #
    vk
    cZ
    wrex
    #
    @9
    @11
    @14
    vk
    @2
    cuz
    cfv
    wral
    vj
    cZ
    wrex
    #
    @15
    wph
    cM
    cz
    wcel
    @10
    @16
    iscmet3.3
    @5
    vj
    vk
    cM
    cZ
    iscmet3.1
    iscmet3lem3
    sylan
    @14
    vj
    vk
    cM
    cZ
    iscmet3.1
    r19.2uz
    syl
    @11
    @14
    @8
    vk
    cZ
    @11
    @0
    cZ
    wcel
    #
    wa
    @14
    @6
    vj
    @7
    @11
    @17
    @2
    @7
    wcel
    #
    @14
    @6
    wi
    @11
    @17
    @18
    wa
    #
    wa
    #
    @4
    @13
    clt
    wbr
    #
    @14
    @6
    @20
    @1
    @0
    cS
    cfv
    #
    wcel
    #
    @3
    @22
    wcel
    #
    vu
    cv
    #
    vv
    cv
    #
    cD
    co
    #
    @13
    clt
    wbr
    #
    vv
    @22
    wral
    vu
    @22
    wral
    #
    @21
    @20
    @0
    cM
    @0
    cfz
    co
    #
    wcel
    #
    @1
    vn
    cv
    #
    cS
    cfv
    #
    wcel
    #
    vn
    @30
    wral
    #
    @23
    @20
    @0
    cM
    cuz
    cfv
    #
    wcel
    #
    @31
    @20
    @0
    cZ
    @36
    @19
    @17
    @11
    @17
    @18
    simpl
    #
    adantl
    #
    iscmet3.1
    syl6eleq
    #
    cM
    @0
    eluzfz2
    syl
    @20
    @35
    vk
    cZ
    wral
    #
    @17
    @35
    wph
    @41
    @10
    @19
    iscmet3.10
    ad2antrr
    #
    @39
    @35
    vk
    cZ
    rsp
    sylc
    @34
    @23
    vn
    @0
    @30
    @32
    @0
    wceq
    #
    @33
    @22
    @1
    @32
    @0
    cS
    fveq2
    #
    eleq2d
    rspcv
    sylc
    @20
    @0
    cM
    @2
    cfz
    co
    #
    wcel
    #
    @3
    @33
    wcel
    #
    vn
    @45
    wral
    #
    @24
    @20
    @37
    @18
    @46
    @40
    @11
    @17
    @18
    simprr
    @0
    cM
    @2
    elfzuzb
    sylanbrc
    @20
    @2
    cZ
    wcel
    #
    @41
    @48
    @19
    @49
    @11
    cM
    @2
    @0
    cZ
    iscmet3.1
    uztrn2
    #
    adantl
    @42
    @35
    @48
    vk
    @2
    cZ
    @0
    @2
    wceq
    #
    @34
    @47
    vn
    @30
    @45
    @0
    @2
    cM
    cfz
    oveq2
    @51
    @1
    @3
    @33
    @0
    @2
    cF
    fveq2
    eleq1d
    raleqbidv
    rspcv
    sylc
    @47
    @24
    vn
    @0
    @45
    @43
    @33
    @22
    @3
    @44
    eleq2d
    rspcv
    sylc
    @20
    @29
    vk
    cz
    wral
    #
    @0
    cz
    wcel
    #
    @29
    wph
    @52
    @10
    @19
    iscmet3.9
    ad2antrr
    @17
    @53
    @11
    @18
    @53
    @0
    @36
    cZ
    cM
    @0
    eluzelz
    iscmet3.1
    eleq2s
    ad2antrl
    #
    @29
    vk
    cz
    rsp
    sylc
    @28
    @21
    @1
    @26
    cD
    co
    #
    @13
    clt
    wbr
    vu
    vv
    @1
    @3
    @22
    @22
    @25
    @1
    wceq
    @27
    @55
    @13
    clt
    @25
    @1
    @26
    cD
    oveq1
    breq1d
    @26
    @3
    wceq
    @55
    @4
    @13
    clt
    @26
    @3
    @1
    cD
    oveq2
    breq1d
    rspc2va
    syl21anc
    @20
    @4
    cr
    wcel
    #
    @13
    cr
    wcel
    @5
    cr
    wcel
    #
    @21
    @14
    wa
    @6
    wi
    @20
    cD
    cX
    cme
    cfv
    wcel
    #
    @1
    cX
    wcel
    #
    @3
    cX
    wcel
    #
    @56
    wph
    @58
    @10
    @19
    iscmet3.4
    ad2antrr
    @11
    cZ
    cX
    cF
    wf
    #
    @17
    @59
    @19
    wph
    @61
    @10
    iscmet3.6
    adantr
    #
    @38
    cZ
    cX
    @0
    cF
    ffvelrn
    syl2an
    @11
    @61
    @49
    @60
    @19
    @62
    @50
    cZ
    cX
    @2
    cF
    ffvelrn
    syl2an
    @1
    @3
    cD
    cX
    metcl
    syl3anc
    @20
    @13
    @20
    @12
    crp
    wcel
    #
    @53
    @13
    crp
    wcel
    c1
    crp
    wcel
    @63
    1rp
    c1
    rphalfcl
    ax-mp
    @54
    @12
    @0
    rpexpcl
    sylancr
    rpred
    @10
    @57
    wph
    @19
    @5
    rpre
    ad2antlr
    @4
    @13
    @5
    lttr
    syl3anc
    mpand
    anassrs
    ralrimdva
    reximdva
    mpd
    ralrimiva
    wph
    vr
    @3
    @1
    cD
    vk
    vj
    cF
    cM
    cX
    cZ
    iscmet3.1
    wph
    @58
    cD
    cX
    cxmt
    cfv
    wcel
    iscmet3.4
    cD
    cX
    metxmet
    syl
    iscmet3.3
    wph
    @49
    wa
    @3
    eqidd
    wph
    @17
    wa
    @1
    eqidd
    iscmet3.6
    iscauf
    mpbird
end
