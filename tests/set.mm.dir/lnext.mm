include "co.mm"
include "wcel.mm"
include "cs3.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "wa.mm"
include "wceq.mm"
include "axtgsegcon.mm"
include "adantr.mm"
include "cstrkg.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "simprr.mm"
include "eqcomd.mm"
include "simpllr.mm"
include "simprl.mm"
include "tgcgrextend.mm"
include "tgcgrcomlr.mm"
include "trgcgr.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "simpr.mm"
include "tgcgrxfr.mm"
include "cgr3swap23.mm"
include "wo.mm"
include "w3o.mm"
include "tgcolg.mm"
include "mpbid.mm"
include "mpjao3dan.mm"

theorem lnext
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let c.sm: class .~
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume tglngval.p: |- P = ( Base ` G )
  assume tglngval.l: |- L = ( LineG ` G )
  assume tglngval.i: |- I = ( Itv ` G )
  assume tglngval.g: |- ( ph -> G e. TarskiG )
  assume tglngval.x: |- ( ph -> X e. P )
  assume tglngval.y: |- ( ph -> Y e. P )
  assume tgcolg.z: |- ( ph -> Z e. P )
  assume lnxfr.r: |- .~ = ( cgrG ` G )
  assume lnxfr.a: |- ( ph -> A e. P )
  assume lnxfr.b: |- ( ph -> B e. P )
  assume lnxfr.d: |- .- = ( dist ` G )
  assume lnext.1: |- ( ph -> ( Y e. ( X L Z ) \/ X = Z ) )
  assume lnext.2: |- ( ph -> ( X .- Y ) = ( A .- B ) )

  disjoint .- c
  disjoint .~ c
  disjoint A c
  disjoint B c
  disjoint I c
  disjoint P c
  disjoint X c
  disjoint Y c
  disjoint Z c
  disjoint c ph
  disjoint x y
  disjoint x z
  disjoint G x
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> E. c e. P <" X Y Z "> .~ <" A B c "> )

  proof
    wph
    cY
    cX
    cZ
    cI
    co
    wcel
    #
    cX
    cY
    cZ
    cs3
    cA
    cB
    vc
    cv
    #
    cs3
    c.sm
    wbr
    #
    vc
    cP
    wrex
    #
    cX
    cY
    cZ
    cI
    co
    wcel
    #
    cZ
    cX
    cY
    cI
    co
    wcel
    #
    wph
    @0
    wa
    #
    cB
    cA
    @1
    cI
    co
    wcel
    #
    cB
    @1
    c.mi
    co
    #
    cY
    cZ
    c.mi
    co
    #
    wceq
    #
    wa
    #
    vc
    cP
    wrex
    #
    @3
    wph
    @12
    @0
    wph
    vc
    cY
    cZ
    cP
    cG
    cI
    c.mi
    cA
    cB
    tglngval.p
    lnxfr.d
    tglngval.i
    tglngval.g
    lnxfr.a
    lnxfr.b
    tglngval.y
    tgcolg.z
    axtgsegcon
    adantr
    @6
    @11
    @2
    vc
    cP
    @6
    @1
    cP
    wcel
    #
    wa
    #
    @11
    @2
    @14
    @11
    wa
    #
    cX
    cY
    cZ
    cA
    cP
    c.sm
    cB
    @1
    cG
    c.mi
    tglngval.p
    lnxfr.d
    lnxfr.r
    wph
    cG
    cstrkg
    wcel
    #
    @0
    @13
    @11
    tglngval.g
    ad3antrrr
    #
    wph
    cX
    cP
    wcel
    #
    @0
    @13
    @11
    tglngval.x
    ad3antrrr
    #
    wph
    cY
    cP
    wcel
    #
    @0
    @13
    @11
    tglngval.y
    ad3antrrr
    #
    wph
    cZ
    cP
    wcel
    #
    @0
    @13
    @11
    tgcolg.z
    ad3antrrr
    #
    wph
    cA
    cP
    wcel
    #
    @0
    @13
    @11
    lnxfr.a
    ad3antrrr
    #
    wph
    cB
    cP
    wcel
    #
    @0
    @13
    @11
    lnxfr.b
    ad3antrrr
    #
    @6
    @13
    @11
    simplr
    #
    wph
    cX
    cY
    c.mi
    co
    cA
    cB
    c.mi
    co
    wceq
    #
    @0
    @13
    @11
    lnext.2
    ad3antrrr
    #
    @15
    @8
    @9
    @14
    @7
    @10
    simprr
    eqcomd
    #
    @15
    cX
    cZ
    cA
    @1
    cP
    cG
    cI
    c.mi
    tglngval.p
    lnxfr.d
    tglngval.i
    @17
    @19
    @23
    @25
    @28
    @15
    cX
    cY
    cZ
    cA
    cP
    cB
    @1
    cG
    cI
    c.mi
    tglngval.p
    lnxfr.d
    tglngval.i
    @17
    @19
    @21
    @23
    @25
    @27
    @28
    wph
    @0
    @13
    @11
    simpllr
    @14
    @7
    @10
    simprl
    @30
    @31
    tgcgrextend
    tgcgrcomlr
    trgcgr
    ex
    reximdva
    mpd
    wph
    @4
    wa
    #
    cA
    cB
    @1
    cI
    co
    wcel
    #
    cA
    @1
    c.mi
    co
    #
    cX
    cZ
    c.mi
    co
    #
    wceq
    #
    wa
    #
    vc
    cP
    wrex
    #
    @3
    wph
    @38
    @4
    wph
    vc
    cX
    cZ
    cP
    cG
    cI
    c.mi
    cB
    cA
    tglngval.p
    lnxfr.d
    tglngval.i
    tglngval.g
    lnxfr.b
    lnxfr.a
    tglngval.x
    tgcolg.z
    axtgsegcon
    adantr
    @32
    @37
    @2
    vc
    cP
    @32
    @13
    wa
    #
    @37
    @2
    @39
    @37
    wa
    #
    cX
    cY
    cZ
    cA
    cP
    c.sm
    cB
    @1
    cG
    c.mi
    tglngval.p
    lnxfr.d
    lnxfr.r
    wph
    @16
    @4
    @13
    @37
    tglngval.g
    ad3antrrr
    #
    wph
    @18
    @4
    @13
    @37
    tglngval.x
    ad3antrrr
    #
    wph
    @20
    @4
    @13
    @37
    tglngval.y
    ad3antrrr
    #
    wph
    @22
    @4
    @13
    @37
    tgcolg.z
    ad3antrrr
    #
    wph
    @24
    @4
    @13
    @37
    lnxfr.a
    ad3antrrr
    #
    wph
    @26
    @4
    @13
    @37
    lnxfr.b
    ad3antrrr
    #
    @32
    @13
    @37
    simplr
    #
    wph
    @29
    @4
    @13
    @37
    lnext.2
    ad3antrrr
    #
    @40
    cY
    cX
    cZ
    cB
    cP
    cA
    @1
    cG
    cI
    c.mi
    tglngval.p
    lnxfr.d
    tglngval.i
    @41
    @43
    @42
    @44
    @46
    @45
    @47
    wph
    @4
    @13
    @37
    simpllr
    @39
    @33
    @36
    simprl
    @40
    cX
    cY
    cA
    cB
    cP
    cG
    cI
    c.mi
    tglngval.p
    lnxfr.d
    tglngval.i
    @41
    @42
    @43
    @45
    @46
    @48
    tgcgrcomlr
    @40
    @34
    @35
    @39
    @33
    @36
    simprr
    eqcomd
    #
    tgcgrextend
    @40
    cX
    cZ
    cA
    @1
    cP
    cG
    cI
    c.mi
    tglngval.p
    lnxfr.d
    tglngval.i
    @41
    @42
    @44
    @45
    @47
    @49
    tgcgrcomlr
    trgcgr
    ex
    reximdva
    mpd
    wph
    @5
    wa
    #
    @1
    cA
    cB
    cI
    co
    wcel
    #
    cX
    cZ
    cY
    cs3
    cA
    @1
    cB
    cs3
    c.sm
    wbr
    #
    wa
    #
    vc
    cP
    wrex
    @3
    @50
    cX
    cZ
    cY
    cA
    cP
    c.sm
    vc
    cB
    cG
    cI
    c.mi
    tglngval.p
    lnxfr.d
    tglngval.i
    lnxfr.r
    wph
    @16
    @5
    tglngval.g
    adantr
    wph
    @18
    @5
    tglngval.x
    adantr
    wph
    @22
    @5
    tgcolg.z
    adantr
    wph
    @20
    @5
    tglngval.y
    adantr
    wph
    @24
    @5
    lnxfr.a
    adantr
    wph
    @26
    @5
    lnxfr.b
    adantr
    wph
    @5
    simpr
    wph
    @29
    @5
    lnext.2
    adantr
    tgcgrxfr
    @50
    @53
    @2
    vc
    cP
    @50
    @13
    wa
    #
    @53
    @2
    @54
    @53
    wa
    cX
    cZ
    cY
    cA
    cP
    c.sm
    @1
    cB
    cG
    cI
    c.mi
    tglngval.p
    lnxfr.d
    tglngval.i
    lnxfr.r
    wph
    @16
    @5
    @13
    @53
    tglngval.g
    ad3antrrr
    wph
    @18
    @5
    @13
    @53
    tglngval.x
    ad3antrrr
    wph
    @22
    @5
    @13
    @53
    tgcolg.z
    ad3antrrr
    wph
    @20
    @5
    @13
    @53
    tglngval.y
    ad3antrrr
    wph
    @24
    @5
    @13
    @53
    lnxfr.a
    ad3antrrr
    @50
    @13
    @53
    simplr
    wph
    @26
    @5
    @13
    @53
    lnxfr.b
    ad3antrrr
    @54
    @51
    @52
    simprr
    cgr3swap23
    ex
    reximdva
    mpd
    wph
    cY
    cX
    cZ
    cL
    co
    wcel
    cX
    cZ
    wceq
    wo
    @0
    @4
    @5
    w3o
    lnext.1
    wph
    cP
    cG
    cI
    cL
    cX
    cZ
    cY
    tglngval.p
    tglngval.l
    tglngval.i
    tglngval.g
    tglngval.x
    tgcolg.z
    tglngval.y
    tgcolg
    mpbid
    mpjao3dan
end
