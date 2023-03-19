include "cv.mm"
include "chil.mm"
include "wcel.mm"
include "clf.mm"
include "ccnfn.mm"
include "cc.mm"
include "wf.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "cfv.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "wral.mm"
include "csp.mm"
include "lnopfi.mm"
include "ffvelrni.mm"
include "hicl.mm"
include "sylan.mm"
include "ancoms.mm"
include "fmptd.mm"
include "wa.mm"
include "hvmulcl.mm"
include "w3a.mm"
include "lnopaddi.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "id.mm"
include "ax-his2.mm"
include "syl3an.mm"
include "eqtrd.mm"
include "3comr.mm"
include "3expa.mm"
include "sylanl2.mm"
include "hvaddcl.mm"
include "cnlnadjlem1.mm"
include "syl.mm"
include "adantll.mm"
include "ax-his3.mm"
include "syl3an2.mm"
include "3expb.mm"
include "lnopmuli.mm"
include "adantl.mm"
include "oveq2d.mm"
include "ad2antll.mm"
include "3eqtr4rd.mm"
include "oveqan12d.mm"
include "3eqtr4d.mm"
include "ralrimiva.mm"
include "ralrimivva.mm"
include "ellnfn.mm"
include "sylanbrc.mm"
include "cabs.mm"
include "cno.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "wrex.mm"
include "cnop.mm"
include "nmcopexi.mm"
include "normcl.mm"
include "remulcl.mm"
include "sylancr.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "abscld.mm"
include "syl2an.mm"
include "fveq2d.mm"
include "bcs.mm"
include "eqbrtrd.mm"
include "cc0.mm"
include "normge0.mm"
include "jca.mm"
include "nmcoplbi.mm"
include "lemul1a.mm"
include "syl31anc.mm"
include "letrd.mm"
include "recnd.mm"
include "recni.mm"
include "mul32.mm"
include "mp3an1.mm"
include "breqtrd.mm"
include "oveq1.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wb.mm"
include "lnfncon.mm"
include "mpbird.mm"

theorem cnlnadjlem2
  let vy: setvar y
  let cT: class T
  let vg: setvar g
  let cG: class G
  let vf: setvar f
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vt: setvar t
  let vx: setvar x
  let cF: class F
  let cC: class C
  assume cnlnadjlem.1: |- T e. LinOp
  assume cnlnadjlem.2: |- T e. ContOp
  assume cnlnadjlem.3: |- G = ( g e. ~H |-> ( ( T ` g ) .ih y ) )

  disjoint g y
  disjoint T g
  disjoint T y
  disjoint f g
  disjoint f v
  disjoint f w
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g v
  disjoint g w
  disjoint g z
  disjoint A g
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B z
  disjoint f t
  disjoint f x
  disjoint F f
  disjoint t w
  disjoint t x
  disjoint t z
  disjoint F t
  disjoint w x
  disjoint F w
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint T f
  disjoint g t
  disjoint g x
  disjoint t v
  disjoint t y
  disjoint T t
  disjoint v x
  disjoint T v
  disjoint T w
  disjoint x y
  disjoint T x
  disjoint T z
  disjoint C f
  disjoint G f
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G z
  assert |- ( y e. ~H -> ( G e. LinFn /\ G e. ContFn ) )

  proof
    vy
    cv
    #
    chil
    wcel
    #
    cG
    clf
    wcel
    #
    cG
    ccnfn
    wcel
    #
    @1
    chil
    cc
    cG
    wf
    vx
    cv
    #
    vw
    cv
    #
    csm
    co
    #
    vz
    cv
    #
    cva
    co
    #
    cG
    cfv
    #
    @4
    @5
    cG
    cfv
    #
    cmul
    co
    #
    @7
    cG
    cfv
    #
    caddc
    co
    #
    wceq
    #
    vz
    chil
    wral
    #
    vw
    chil
    wral
    vx
    cc
    wral
    @2
    @1
    vg
    chil
    vg
    cv
    #
    cT
    cfv
    #
    @0
    csp
    co
    #
    cc
    cG
    @16
    chil
    wcel
    #
    @1
    @18
    cc
    wcel
    #
    @19
    @17
    chil
    wcel
    @1
    @20
    chil
    chil
    @16
    cT
    cT
    cnlnadjlem.1
    lnopfi
    #
    ffvelrni
    @17
    @0
    hicl
    sylan
    ancoms
    cnlnadjlem.3
    fmptd
    @1
    @15
    vx
    vw
    cc
    chil
    @1
    @4
    cc
    wcel
    #
    @5
    chil
    wcel
    #
    wa
    #
    wa
    #
    @14
    vz
    chil
    @25
    @7
    chil
    wcel
    #
    wa
    @8
    cT
    cfv
    #
    @0
    csp
    co
    #
    @6
    cT
    cfv
    #
    @0
    csp
    co
    #
    @7
    cT
    cfv
    #
    @0
    csp
    co
    #
    caddc
    co
    #
    @9
    @13
    @24
    @1
    @6
    chil
    wcel
    #
    @26
    @28
    @33
    wceq
    #
    @4
    @5
    hvmulcl
    #
    @1
    @34
    @26
    @35
    @34
    @26
    @1
    @35
    @34
    @26
    @1
    w3a
    #
    @28
    @29
    @31
    cva
    co
    #
    @0
    csp
    co
    #
    @33
    @37
    @27
    @38
    @0
    csp
    @34
    @26
    @27
    @38
    wceq
    @1
    @6
    @7
    cT
    cnlnadjlem.1
    lnopaddi
    3adant3
    oveq1d
    @34
    @29
    chil
    wcel
    @26
    @31
    chil
    wcel
    #
    @1
    @1
    @39
    @33
    wceq
    chil
    chil
    @6
    cT
    @21
    ffvelrni
    chil
    chil
    @7
    cT
    @21
    ffvelrni
    #
    @1
    id
    @29
    @31
    @0
    ax-his2
    syl3an
    eqtrd
    3comr
    3expa
    sylanl2
    @24
    @26
    @9
    @28
    wceq
    #
    @1
    @24
    @26
    wa
    @8
    chil
    wcel
    #
    @42
    @24
    @34
    @26
    @43
    @36
    @6
    @7
    hvaddcl
    sylan
    vy
    @8
    cT
    vg
    cG
    cnlnadjlem.1
    cnlnadjlem.2
    cnlnadjlem.3
    cnlnadjlem1
    syl
    adantll
    @25
    @26
    @11
    @30
    @12
    @32
    caddc
    @25
    @4
    @5
    cT
    cfv
    #
    csm
    co
    #
    @0
    csp
    co
    #
    @4
    @44
    @0
    csp
    co
    #
    cmul
    co
    #
    @30
    @11
    @1
    @22
    @23
    @46
    @48
    wceq
    #
    @22
    @23
    @1
    @49
    @23
    @22
    @44
    chil
    wcel
    @1
    @49
    chil
    chil
    @5
    cT
    @21
    ffvelrni
    @4
    @44
    @0
    ax-his3
    syl3an2
    3comr
    3expb
    @24
    @30
    @46
    wceq
    @1
    @24
    @29
    @45
    @0
    csp
    @4
    @5
    cT
    cnlnadjlem.1
    lnopmuli
    oveq1d
    adantl
    @23
    @11
    @48
    wceq
    @1
    @22
    @23
    @10
    @47
    @4
    cmul
    vy
    @5
    cT
    vg
    cG
    cnlnadjlem.1
    cnlnadjlem.2
    cnlnadjlem.3
    cnlnadjlem1
    oveq2d
    ad2antll
    3eqtr4rd
    vy
    @7
    cT
    vg
    cG
    cnlnadjlem.1
    cnlnadjlem.2
    cnlnadjlem.3
    cnlnadjlem1
    #
    oveqan12d
    3eqtr4d
    ralrimiva
    ralrimivva
    vx
    vw
    vz
    cG
    ellnfn
    sylanbrc
    #
    @1
    @3
    @12
    cabs
    cfv
    #
    @4
    @7
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vz
    chil
    wral
    #
    vx
    cr
    wrex
    #
    @1
    cT
    cnop
    cfv
    #
    @0
    cno
    cfv
    #
    cmul
    co
    #
    cr
    wcel
    #
    @52
    @60
    @53
    cmul
    co
    #
    cle
    wbr
    #
    vz
    chil
    wral
    #
    @57
    @1
    @58
    cr
    wcel
    #
    @59
    cr
    wcel
    #
    @61
    cT
    cnlnadjlem.1
    cnlnadjlem.2
    nmcopexi
    #
    @0
    normcl
    #
    @58
    @59
    remulcl
    sylancr
    @1
    @63
    vz
    chil
    @26
    @1
    @63
    @26
    @1
    wa
    #
    @52
    @58
    @53
    cmul
    co
    #
    @59
    cmul
    co
    #
    @62
    cle
    @69
    @52
    @31
    cno
    cfv
    #
    @59
    cmul
    co
    #
    @71
    @69
    @12
    @69
    @12
    @32
    cc
    @26
    @12
    @32
    wceq
    @1
    @50
    adantr
    #
    @26
    @40
    @1
    @32
    cc
    wcel
    @41
    @31
    @0
    hicl
    sylan
    eqeltrd
    abscld
    @26
    @72
    cr
    wcel
    #
    @66
    @73
    cr
    wcel
    @1
    @26
    @40
    @75
    @41
    @31
    normcl
    syl
    #
    @68
    @72
    @59
    remulcl
    syl2an
    @26
    @70
    cr
    wcel
    #
    @66
    @71
    cr
    wcel
    @1
    @26
    @65
    @53
    cr
    wcel
    @77
    @67
    @7
    normcl
    #
    @58
    @53
    remulcl
    sylancr
    #
    @68
    @70
    @59
    remulcl
    syl2an
    @69
    @52
    @32
    cabs
    cfv
    #
    @73
    cle
    @69
    @12
    @32
    cabs
    @74
    fveq2d
    @26
    @40
    @1
    @80
    @73
    cle
    wbr
    @41
    @31
    @0
    bcs
    sylan
    eqbrtrd
    @69
    @75
    @77
    @66
    cc0
    @59
    cle
    wbr
    #
    wa
    #
    @72
    @70
    cle
    wbr
    #
    @73
    @71
    cle
    wbr
    @26
    @75
    @1
    @76
    adantr
    @26
    @77
    @1
    @79
    adantr
    @1
    @82
    @26
    @1
    @66
    @81
    @68
    @0
    normge0
    jca
    adantl
    @26
    @83
    @1
    @7
    cT
    cnlnadjlem.1
    cnlnadjlem.2
    nmcoplbi
    adantr
    @72
    @70
    @59
    lemul1a
    syl31anc
    letrd
    @26
    @53
    cc
    wcel
    #
    @59
    cc
    wcel
    #
    @71
    @62
    wceq
    #
    @1
    @26
    @53
    @78
    recnd
    @1
    @59
    @68
    recnd
    @58
    cc
    wcel
    @84
    @85
    @86
    @58
    @67
    recni
    @58
    @53
    @59
    mul32
    mp3an1
    syl2an
    breqtrd
    ancoms
    ralrimiva
    @56
    @64
    vx
    @60
    cr
    @4
    @60
    wceq
    #
    @55
    @63
    vz
    chil
    @87
    @54
    @62
    @52
    cle
    @4
    @60
    @53
    cmul
    oveq1
    breq2d
    ralbidv
    rspcev
    syl2anc
    @1
    @2
    @3
    @57
    wb
    @51
    vx
    vz
    cG
    lnfncon
    syl
    mpbird
    jca
end
