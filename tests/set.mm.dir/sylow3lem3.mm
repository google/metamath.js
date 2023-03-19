include "cslw.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cqg.mm"
include "cqs.mm"
include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "cpw.mm"
include "wss.mm"
include "pwfi.mm"
include "sylib.mm"
include "cv.mm"
include "csubg.mm"
include "slwsubg.mm"
include "subgss.mm"
include "syl.mm"
include "selpw.mm"
include "sylibr.mm"
include "ssriv.mm"
include "ssfi.mm"
include "sylancl.mm"
include "hashcl.mm"
include "nn0cnd.mm"
include "cgrp.mm"
include "wer.mm"
include "nmzsubg.mm"
include "eqid.mm"
include "eqger.mm"
include "3syl.mm"
include "qsss.mm"
include "syl2anc.mm"
include "cn.mm"
include "c0.mm"
include "wne.mm"
include "c0g.mm"
include "subg0cl.mm"
include "ne0i.mm"
include "wb.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "cpr.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "copab.mm"
include "cec.mm"
include "cmul.mm"
include "cga.mm"
include "sylow3lem1.mm"
include "orbsta2.mm"
include "syl21anc.mm"
include "lagsubg2.mm"
include "gaorber.mm"
include "ecss.mm"
include "wbr.mm"
include "adantr.mm"
include "simpr.mm"
include "cmpt.mm"
include "crn.mm"
include "sylow2.mm"
include "eqcom.mm"
include "cvv.mm"
include "mptexg.mm"
include "rnexg.mm"
include "simpl.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "mpteq12dv.mm"
include "rneqd.mm"
include "ovmpt2ga.mm"
include "syl3anc.mm"
include "eqeq2d.mm"
include "syl5bb.mm"
include "rexbidva.mm"
include "gaorb.mm"
include "syl3anbrc.mm"
include "elecg.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "fveq2d.mm"
include "sylow3lem2.mm"
include "3eqtr3rd.mm"
include "mulcan2ad.mm"

theorem sylow3lem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let cP: class P
  let c.pl: class .+
  let c.po: class .(+)
  let cG: class G
  let cH: class H
  let cK: class K
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vv: setvar v
  let vw: setvar w
  let vg: setvar g
  let vh: setvar h
  let vs: setvar s
  let vk: setvar k
  assume sylow3.x: |- X = ( Base ` G )
  assume sylow3.g: |- ( ph -> G e. Grp )
  assume sylow3.xf: |- ( ph -> X e. Fin )
  assume sylow3.p: |- ( ph -> P e. Prime )
  assume sylow3lem1.a: |- .+ = ( +g ` G )
  assume sylow3lem1.d: |- .- = ( -g ` G )
  assume sylow3lem1.m: |- .(+) = ( x e. X , y e. ( P pSyl G ) |-> ran ( z e. y |-> ( ( x .+ z ) .- x ) ) )
  assume sylow3lem2.k: |- ( ph -> K e. ( P pSyl G ) )
  assume sylow3lem2.h: |- H = { u e. X | ( u .(+) K ) = K }
  assume sylow3lem2.n: |- N = { x e. X | A. y e. X ( ( x .+ y ) e. K <-> ( y .+ x ) e. K ) }

  disjoint u x
  disjoint u y
  disjoint u z
  disjoint .- u
  disjoint x y
  disjoint x z
  disjoint .- x
  disjoint y z
  disjoint .- y
  disjoint .- z
  disjoint .(+) u
  disjoint .(+) x
  disjoint .(+) y
  disjoint .(+) z
  disjoint H x
  disjoint H y
  disjoint K u
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint N u
  disjoint N z
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint G u
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint ph u
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint .+ u
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint P u
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint a b
  disjoint a c
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint .- a
  disjoint b c
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint .- b
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint .- c
  disjoint u v
  disjoint u w
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint .- v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint .- w
  disjoint a g
  disjoint a h
  disjoint a s
  disjoint .(+) a
  disjoint b g
  disjoint b h
  disjoint b s
  disjoint .(+) b
  disjoint c g
  disjoint c h
  disjoint c s
  disjoint .(+) c
  disjoint g h
  disjoint g s
  disjoint g u
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint .(+) g
  disjoint h s
  disjoint h u
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint .(+) h
  disjoint s u
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint .(+) s
  disjoint .(+) w
  disjoint H g
  disjoint g v
  disjoint K g
  disjoint h v
  disjoint K h
  disjoint s v
  disjoint K s
  disjoint K v
  disjoint K w
  disjoint g k
  disjoint N g
  disjoint k u
  disjoint k w
  disjoint k z
  disjoint N k
  disjoint N w
  disjoint a k
  disjoint X a
  disjoint b k
  disjoint X b
  disjoint c k
  disjoint X c
  disjoint X g
  disjoint h k
  disjoint X h
  disjoint k x
  disjoint k y
  disjoint X k
  disjoint X w
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G g
  disjoint G h
  disjoint k s
  disjoint G k
  disjoint G s
  disjoint G w
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint g ph
  disjoint h ph
  disjoint k ph
  disjoint ph s
  disjoint ph w
  disjoint .+ a
  disjoint .+ b
  disjoint .+ c
  disjoint .+ g
  disjoint .+ v
  disjoint .+ w
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P g
  disjoint P h
  disjoint P k
  disjoint P s
  disjoint P w
  assert |- ( ph -> ( # ` ( P pSyl G ) ) = ( # ` ( X /. ( G ~QG N ) ) ) )

  proof
    wph
    cP
    cG
    cslw
    co
    #
    chash
    cfv
    #
    cX
    cG
    cN
    cqg
    co
    #
    cqs
    #
    chash
    cfv
    #
    cN
    chash
    cfv
    #
    wph
    @1
    wph
    @0
    cfn
    wcel
    #
    @1
    cn0
    wcel
    wph
    cX
    cpw
    #
    cfn
    wcel
    #
    @0
    @7
    wss
    @6
    wph
    cX
    cfn
    wcel
    #
    @8
    sylow3.xf
    cX
    pwfi
    sylib
    #
    vx
    @0
    @7
    vx
    cv
    #
    @0
    wcel
    #
    @11
    cX
    wss
    #
    @11
    @7
    wcel
    @12
    @11
    cG
    csubg
    cfv
    #
    wcel
    @13
    cP
    cG
    @11
    slwsubg
    cX
    @11
    cG
    sylow3.x
    subgss
    syl
    vx
    cX
    selpw
    sylibr
    ssriv
    @7
    @0
    ssfi
    sylancl
    @0
    hashcl
    syl
    nn0cnd
    wph
    @4
    wph
    @3
    cfn
    wcel
    #
    @4
    cn0
    wcel
    wph
    @8
    @3
    @7
    wss
    @15
    @10
    wph
    cX
    @2
    wph
    cG
    cgrp
    wcel
    #
    cN
    @14
    wcel
    #
    cX
    @2
    wer
    sylow3.g
    vx
    vy
    c.pl
    cK
    cG
    cN
    cX
    sylow3lem2.n
    sylow3.x
    sylow3lem1.a
    nmzsubg
    #
    @2
    cG
    cX
    cN
    sylow3.x
    @2
    eqid
    #
    eqger
    3syl
    qsss
    @7
    @3
    ssfi
    syl2anc
    @3
    hashcl
    syl
    nn0cnd
    wph
    @5
    wph
    @5
    cn
    wcel
    #
    cN
    c0
    wne
    #
    wph
    @17
    cG
    c0g
    cfv
    #
    cN
    wcel
    @21
    wph
    @16
    @17
    sylow3.g
    @18
    syl
    #
    cN
    cG
    @22
    @22
    eqid
    subg0cl
    cN
    @22
    ne0i
    3syl
    wph
    cN
    cfn
    wcel
    #
    @20
    @21
    wb
    wph
    @9
    cN
    cX
    wss
    #
    @24
    sylow3.xf
    wph
    @16
    @17
    @25
    sylow3.g
    @18
    cX
    cN
    cG
    sylow3.x
    subgss
    3syl
    cX
    cN
    ssfi
    syl2anc
    cN
    hashnncl
    syl
    mpbird
    #
    nncnd
    wph
    @5
    @26
    nnne0d
    wph
    cX
    chash
    cfv
    #
    cK
    @11
    vy
    cv
    #
    cpr
    @0
    wss
    vg
    cv
    @11
    c.po
    co
    @28
    wceq
    vg
    cX
    wrex
    wa
    vx
    vy
    copab
    #
    cec
    #
    chash
    cfv
    #
    cH
    chash
    cfv
    #
    cmul
    co
    #
    @4
    @5
    cmul
    co
    @1
    @5
    cmul
    co
    wph
    c.po
    cG
    @0
    cga
    co
    wcel
    #
    cK
    @0
    wcel
    #
    @9
    @27
    @33
    wceq
    wph
    vx
    vy
    vz
    cP
    c.pl
    c.po
    cG
    c.mi
    cX
    sylow3.x
    sylow3.g
    sylow3.xf
    sylow3.p
    sylow3lem1.a
    sylow3lem1.d
    sylow3lem1.m
    sylow3lem1
    #
    sylow3lem2.k
    sylow3.xf
    vx
    vy
    vu
    cK
    c.po
    cG
    cH
    cqg
    co
    #
    vg
    cG
    cH
    @29
    cX
    @0
    sylow3.x
    sylow3lem2.h
    @37
    eqid
    @29
    eqid
    #
    orbsta2
    syl21anc
    wph
    @2
    cG
    cX
    cN
    sylow3.x
    @19
    @23
    sylow3.xf
    lagsubg2
    wph
    @31
    @1
    @32
    @5
    cmul
    wph
    @30
    @0
    chash
    wph
    @30
    @0
    wph
    cK
    @29
    @0
    wph
    @34
    @0
    @29
    wer
    @36
    vx
    vy
    c.po
    @29
    vg
    cG
    cX
    @0
    @38
    sylow3.x
    gaorber
    syl
    ecss
    wph
    vh
    @0
    @30
    wph
    vh
    cv
    #
    @0
    wcel
    #
    @39
    @30
    wcel
    #
    wph
    @40
    wa
    #
    @41
    cK
    @39
    @29
    wbr
    #
    @42
    @35
    @40
    vu
    cv
    #
    cK
    c.po
    co
    #
    @39
    wceq
    #
    vu
    cX
    wrex
    #
    @43
    wph
    @35
    @40
    sylow3lem2.k
    adantr
    #
    wph
    @40
    simpr
    #
    @42
    @47
    @39
    vz
    cK
    @44
    vz
    cv
    #
    c.pl
    co
    #
    @44
    c.mi
    co
    #
    cmpt
    #
    crn
    #
    wceq
    #
    vu
    cX
    wrex
    @42
    vz
    cP
    c.pl
    vu
    cG
    @39
    cK
    c.mi
    cX
    sylow3.x
    wph
    @9
    @40
    sylow3.xf
    adantr
    @49
    @48
    sylow3lem1.a
    sylow3lem1.d
    sylow2
    @42
    @46
    @55
    vu
    cX
    @46
    @39
    @45
    wceq
    @42
    @44
    cX
    wcel
    #
    wa
    #
    @55
    @45
    @39
    eqcom
    @57
    @45
    @54
    @39
    @57
    @56
    @35
    @54
    cvv
    wcel
    #
    @45
    @54
    wceq
    @42
    @56
    simpr
    @42
    @35
    @56
    @48
    adantr
    #
    @57
    @35
    @53
    cvv
    wcel
    @58
    @59
    vz
    cK
    @52
    @0
    mptexg
    @53
    cvv
    rnexg
    3syl
    vx
    vy
    @44
    cK
    cX
    @0
    vz
    @28
    @11
    @50
    c.pl
    co
    #
    @11
    c.mi
    co
    #
    cmpt
    #
    crn
    @54
    c.po
    cvv
    @11
    @44
    wceq
    #
    @28
    cK
    wceq
    #
    wa
    #
    @62
    @53
    @65
    vz
    @28
    @61
    cK
    @52
    @63
    @64
    simpr
    @65
    @60
    @51
    @11
    @44
    c.mi
    @65
    @11
    @44
    @50
    c.pl
    @63
    @64
    simpl
    #
    oveq1d
    @66
    oveq12d
    mpteq12dv
    rneqd
    sylow3lem1.m
    ovmpt2ga
    syl3anc
    eqeq2d
    syl5bb
    rexbidva
    mpbird
    vx
    vy
    cK
    @39
    c.po
    @29
    vg
    vu
    cX
    @0
    @38
    gaorb
    syl3anbrc
    @42
    @40
    @35
    @41
    @43
    wb
    @49
    @48
    @39
    cK
    @29
    @0
    @0
    elecg
    syl2anc
    mpbird
    ex
    ssrdv
    eqssd
    fveq2d
    wph
    cH
    cN
    chash
    wph
    vx
    vy
    vz
    vu
    cP
    c.pl
    c.po
    cG
    cH
    cK
    c.mi
    cN
    cX
    sylow3.x
    sylow3.g
    sylow3.xf
    sylow3.p
    sylow3lem1.a
    sylow3lem1.d
    sylow3lem1.m
    sylow3lem2.k
    sylow3lem2.h
    sylow3lem2.n
    sylow3lem2
    fveq2d
    oveq12d
    3eqtr3rd
    mulcan2ad
end
