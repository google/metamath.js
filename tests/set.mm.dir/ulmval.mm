include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "culm.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "cuz.mm"
include "cc.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "cmin.mm"
include "cabs.mm"
include "clt.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "w3a.mm"
include "cz.mm"
include "wi.mm"
include "wrel.mm"
include "ulmrel.mm"
include "brrelex12.mm"
include "mpan.mm"
include "a1i.mm"
include "3simpa.mm"
include "fvex.mm"
include "fex.mm"
include "mpan2.mm"
include "expcom.mm"
include "anim12d.mm"
include "syl5.mm"
include "rexlimdvw.mm"
include "wb.mm"
include "copab.mm"
include "wceq.mm"
include "elex.mm"
include "cpm.mm"
include "cxp.mm"
include "wss.mm"
include "simpr1.mm"
include "uzssz.mm"
include "ovex.mm"
include "zex.mm"
include "elpm2r.mm"
include "mpanl12.mm"
include "sylancl.mm"
include "simpr2.mm"
include "cnex.mm"
include "simpl.mm"
include "elmapg.mm"
include "sylancr.mm"
include "mpbird.mm"
include "jca.mm"
include "ex.mm"
include "ssopab2dv.mm"
include "df-xp.mm"
include "syl6sseqr.mm"
include "xpex.mm"
include "ssex.mm"
include "syl.mm"
include "oveq2.mm"
include "feq3d.mm"
include "feq2.mm"
include "raleq.mm"
include "rexralbidv.mm"
include "ralbidv.mm"
include "3anbi123d.mm"
include "rexbidv.mm"
include "opabbidv.mm"
include "df-ulm.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "breqd.mm"
include "feq1d.mm"
include "simpr.mm"
include "fveq1d.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "eqid.mm"
include "brabga.mm"
include "sylan9bb.mm"
include "pm5.21ndd.mm"

theorem ulmval
  let vx: setvar x
  let vz: setvar z
  let cS: class S
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cV: class V
  let vf: setvar f
  let vy: setvar y
  let vs: setvar s

  disjoint j k
  disjoint j n
  disjoint j x
  disjoint j z
  disjoint F j
  disjoint k n
  disjoint k x
  disjoint k z
  disjoint F k
  disjoint n x
  disjoint n z
  disjoint F n
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint G j
  disjoint G k
  disjoint G n
  disjoint G x
  disjoint G z
  disjoint S j
  disjoint S k
  disjoint S n
  disjoint S x
  disjoint S z
  disjoint V n
  disjoint f j
  disjoint f k
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint j y
  disjoint k y
  disjoint n y
  disjoint x y
  disjoint y z
  disjoint F y
  disjoint G f
  disjoint G y
  disjoint f s
  disjoint S f
  disjoint j s
  disjoint k s
  disjoint n s
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint S s
  disjoint S y
  disjoint V f
  disjoint V y
  assert |- ( S e. V -> ( F ( ~~>u ` S ) G <-> E. n e. ZZ ( F : ( ZZ>= ` n ) --> ( CC ^m S ) /\ G : S --> CC /\ A. x e. RR+ E. j e. ( ZZ>= ` n ) A. k e. ( ZZ>= ` j ) A. z e. S ( abs ` ( ( ( F ` k ) ` z ) - ( G ` z ) ) ) < x ) ) )

  proof
    cS
    cV
    wcel
    #
    cF
    cvv
    wcel
    #
    cG
    cvv
    wcel
    #
    wa
    #
    cF
    cG
    cS
    culm
    cfv
    #
    wbr
    #
    vn
    cv
    #
    cuz
    cfv
    #
    cc
    cS
    cmap
    co
    #
    cF
    wf
    #
    cS
    cc
    cG
    wf
    #
    vz
    cv
    #
    vk
    cv
    #
    cF
    cfv
    #
    cfv
    #
    @11
    cG
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    vz
    cS
    wral
    #
    vk
    vj
    cv
    cuz
    cfv
    #
    wral
    vj
    @7
    wrex
    #
    vx
    crp
    wral
    #
    w3a
    #
    vn
    cz
    wrex
    #
    @5
    @3
    wi
    @0
    @4
    wrel
    @5
    @3
    cS
    ulmrel
    cF
    cG
    @4
    brrelex12
    mpan
    a1i
    @0
    @24
    @3
    vn
    cz
    @24
    @9
    @10
    wa
    @0
    @3
    @9
    @10
    @23
    3simpa
    @0
    @9
    @1
    @10
    @2
    @9
    @1
    wi
    @0
    @9
    @7
    cvv
    wcel
    @1
    @6
    cuz
    fvex
    @7
    @8
    cvv
    cF
    fex
    mpan2
    a1i
    @10
    @0
    @2
    cS
    cc
    cV
    cG
    fex
    expcom
    anim12d
    syl5
    rexlimdvw
    @0
    @3
    @5
    @25
    wb
    @0
    @5
    cF
    cG
    @7
    @8
    vf
    cv
    #
    wf
    #
    cS
    cc
    vy
    cv
    #
    wf
    #
    @11
    @12
    @26
    cfv
    #
    cfv
    #
    @11
    @28
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @18
    clt
    wbr
    #
    vz
    cS
    wral
    #
    vk
    @21
    wral
    vj
    @7
    wrex
    #
    vx
    crp
    wral
    #
    w3a
    #
    vn
    cz
    wrex
    #
    vf
    vy
    copab
    #
    wbr
    @3
    @25
    @0
    @4
    @41
    cF
    cG
    @0
    cS
    cvv
    wcel
    @41
    cvv
    wcel
    #
    @4
    @41
    wceq
    cS
    cV
    elex
    @0
    @41
    @8
    cz
    cpm
    co
    #
    @8
    cxp
    #
    wss
    @42
    @0
    @41
    @26
    @43
    wcel
    #
    @28
    @8
    wcel
    #
    wa
    #
    vf
    vy
    copab
    @44
    @0
    @40
    @47
    vf
    vy
    @0
    @39
    @47
    vn
    cz
    @0
    @39
    @47
    @0
    @39
    wa
    #
    @45
    @46
    @48
    @27
    @7
    cz
    wss
    #
    @45
    @0
    @27
    @29
    @38
    simpr1
    @6
    uzssz
    @8
    cvv
    wcel
    cz
    cvv
    wcel
    @27
    @49
    wa
    @45
    cc
    cS
    cmap
    ovex
    #
    zex
    @8
    cz
    @7
    @26
    cvv
    cvv
    elpm2r
    mpanl12
    sylancl
    @48
    @46
    @29
    @0
    @27
    @29
    @38
    simpr2
    @48
    cc
    cvv
    wcel
    @0
    @46
    @29
    wb
    cnex
    @0
    @39
    simpl
    cc
    cS
    @28
    cvv
    cV
    elmapg
    sylancr
    mpbird
    jca
    ex
    rexlimdvw
    ssopab2dv
    vf
    vy
    @43
    @8
    df-xp
    syl6sseqr
    @41
    @44
    @43
    @8
    @8
    cz
    cpm
    ovex
    @50
    xpex
    ssex
    syl
    vs
    cS
    @7
    cc
    vs
    cv
    #
    cmap
    co
    #
    @26
    wf
    #
    @51
    cc
    @28
    wf
    #
    @35
    vz
    @51
    wral
    #
    vk
    @21
    wral
    vj
    @7
    wrex
    #
    vx
    crp
    wral
    #
    w3a
    #
    vn
    cz
    wrex
    #
    vf
    vy
    copab
    @41
    cvv
    cvv
    culm
    @51
    cS
    wceq
    #
    @59
    @40
    vf
    vy
    @60
    @58
    @39
    vn
    cz
    @60
    @53
    @27
    @54
    @29
    @57
    @38
    @60
    @52
    @8
    @26
    @7
    @51
    cS
    cc
    cmap
    oveq2
    feq3d
    @51
    cS
    cc
    @28
    feq2
    @60
    @56
    @37
    vx
    crp
    @60
    @55
    @36
    vj
    vk
    @7
    @21
    @35
    vz
    @51
    cS
    raleq
    rexralbidv
    ralbidv
    3anbi123d
    rexbidv
    opabbidv
    vx
    vy
    vz
    vf
    vj
    vk
    vn
    vs
    df-ulm
    fvmptg
    syl2anc
    breqd
    @40
    @25
    vf
    vy
    cF
    cG
    @41
    cvv
    cvv
    @26
    cF
    wceq
    #
    @28
    cG
    wceq
    #
    wa
    #
    @39
    @24
    vn
    cz
    @63
    @27
    @9
    @29
    @10
    @38
    @23
    @63
    @7
    @8
    @26
    cF
    @61
    @62
    simpl
    #
    feq1d
    @63
    cS
    cc
    @28
    cG
    @61
    @62
    simpr
    #
    feq1d
    @63
    @37
    @22
    vx
    crp
    @63
    @36
    @20
    vj
    vk
    @7
    @21
    @63
    @35
    @19
    vz
    cS
    @63
    @34
    @17
    @18
    clt
    @63
    @33
    @16
    cabs
    @63
    @31
    @14
    @32
    @15
    cmin
    @63
    @11
    @30
    @13
    @63
    @12
    @26
    cF
    @64
    fveq1d
    fveq1d
    @63
    @11
    @28
    cG
    @65
    fveq1d
    oveq12d
    fveq2d
    breq1d
    ralbidv
    rexralbidv
    ralbidv
    3anbi123d
    rexbidv
    @41
    eqid
    brabga
    sylan9bb
    ex
    pm5.21ndd
end
