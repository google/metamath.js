include "ctb.mm"
include "wcel.mm"
include "cv.mm"
include "ctg.mm"
include "cfv.mm"
include "wss.mm"
include "cuni.mm"
include "wi.mm"
include "wal.mm"
include "cin.mm"
include "wral.mm"
include "ctop.mm"
include "wel.mm"
include "wa.mm"
include "wrex.mm"
include "uniss.mm"
include "adantl.mm"
include "wceq.mm"
include "unitg.mm"
include "adantr.mm"
include "sseqtrd.mm"
include "eluni2.mm"
include "ssel2.mm"
include "eltg2b.mm"
include "rsp.mm"
include "syl6bi.mm"
include "imp31.mm"
include "an32s.mm"
include "sylan2.mm"
include "an42s.mm"
include "elssuni.mm"
include "sstr2.mm"
include "syl5com.mm"
include "anim2d.mm"
include "reximdv.mm"
include "ad2antrl.mm"
include "mpd.mm"
include "rexlimdvaa.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "jca.mm"
include "ex.mm"
include "eltg2.mm"
include "sylibrd.mm"
include "alrimiv.mm"
include "inss1.mm"
include "tg1.mm"
include "syl5ss.mm"
include "simplbda.mm"
include "syl.mm"
include "im2anan9.mm"
include "elin.mm"
include "reeanv.mm"
include "3imtr4g.mm"
include "anandis.mm"
include "biimpri.mm"
include "ss2in.mm"
include "anim12i.mm"
include "an4s.mm"
include "basis2.mm"
include "adantllr.mm"
include "adantrrr.mm"
include "com12.mm"
include "ad2antll.mm"
include "sylanr2.mm"
include "rexlimdva.mm"
include "a2d.mm"
include "imp.mm"
include "syldan.mm"
include "ralrimivv.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "istopg.mm"
include "ax-mp.mm"
include "sylanbrc.mm"

theorem tgcl
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cJ: class J
  let cV: class V
  let cC: class C


  assert |- ( B e. TopBases -> ( topGen ` B ) e. Top )

  proof
    cB
    ctb
    wcel
    #
    vu
    cv
    #
    cB
    ctg
    cfv
    #
    wss
    #
    @1
    cuni
    #
    @2
    wcel
    #
    wi
    #
    vu
    wal
    #
    @1
    vv
    cv
    #
    cin
    #
    @2
    wcel
    #
    vv
    @2
    wral
    vu
    @2
    wral
    #
    @2
    ctop
    wcel
    #
    @0
    @6
    vu
    @0
    @3
    @4
    cB
    cuni
    #
    wss
    #
    vx
    vy
    wel
    #
    vy
    cv
    #
    @4
    wss
    #
    wa
    #
    vy
    cB
    wrex
    #
    vx
    @4
    wral
    #
    wa
    #
    @5
    @0
    @3
    @21
    @0
    @3
    wa
    #
    @14
    @20
    @22
    @4
    @2
    cuni
    #
    @13
    @3
    @4
    @23
    wss
    @0
    @1
    @2
    uniss
    adantl
    @0
    @23
    @13
    wceq
    @3
    cB
    ctb
    unitg
    adantr
    sseqtrd
    @22
    @19
    vx
    @4
    vx
    cv
    #
    @4
    wcel
    vx
    vt
    wel
    #
    vt
    @1
    wrex
    @22
    @19
    vt
    @24
    @1
    eluni2
    @22
    @25
    @19
    vt
    @1
    @22
    vt
    vu
    wel
    #
    @25
    wa
    wa
    @15
    @16
    vt
    cv
    #
    wss
    #
    wa
    #
    vy
    cB
    wrex
    #
    @19
    @0
    @25
    @3
    @26
    @30
    @3
    @26
    wa
    @0
    @25
    wa
    @27
    @2
    wcel
    #
    @30
    @1
    @2
    @27
    ssel2
    @0
    @31
    @25
    @30
    @0
    @31
    @25
    @30
    @0
    @31
    @30
    vx
    @27
    wral
    @25
    @30
    wi
    vx
    vy
    @27
    cB
    ctb
    eltg2b
    @30
    vx
    @27
    rsp
    syl6bi
    imp31
    an32s
    sylan2
    an42s
    @26
    @30
    @19
    wi
    @22
    @25
    @26
    @29
    @18
    vy
    cB
    @26
    @28
    @17
    @15
    @26
    @27
    @4
    wss
    @28
    @17
    @27
    @1
    elssuni
    @16
    @27
    @4
    sstr2
    syl5com
    anim2d
    reximdv
    ad2antrl
    mpd
    rexlimdvaa
    syl5bi
    ralrimiv
    jca
    ex
    vx
    vy
    @4
    cB
    ctb
    eltg2
    sylibrd
    alrimiv
    @0
    @10
    vu
    vv
    @2
    @2
    @0
    @1
    @2
    wcel
    #
    @8
    @2
    wcel
    #
    wa
    #
    @9
    @13
    wss
    #
    @25
    @27
    @9
    wss
    #
    wa
    #
    vt
    cB
    wrex
    #
    vx
    @9
    wral
    #
    wa
    #
    @10
    @0
    @34
    @40
    @0
    @34
    wa
    #
    @35
    @39
    @32
    @35
    @0
    @33
    @32
    @9
    @1
    @13
    @1
    @8
    inss1
    @1
    cB
    tg1
    syl5ss
    ad2antrl
    @41
    @38
    vx
    @9
    @0
    @34
    @24
    @9
    wcel
    #
    vx
    vz
    wel
    #
    vz
    cv
    #
    @1
    wss
    #
    wa
    #
    vx
    vw
    wel
    #
    vw
    cv
    #
    @8
    wss
    #
    wa
    #
    wa
    #
    vw
    cB
    wrex
    #
    vz
    cB
    wrex
    #
    wi
    #
    @42
    @38
    wi
    #
    @0
    @32
    @33
    @54
    @0
    @32
    wa
    #
    @0
    @33
    wa
    #
    wa
    vx
    vu
    wel
    #
    vx
    vv
    wel
    #
    wa
    @46
    vz
    cB
    wrex
    #
    @50
    vw
    cB
    wrex
    #
    wa
    @42
    @53
    @56
    @58
    @60
    @57
    @59
    @61
    @56
    @60
    vx
    @1
    wral
    #
    @58
    @60
    wi
    @0
    @32
    @1
    @13
    wss
    @62
    vx
    vz
    @1
    cB
    ctb
    eltg2
    simplbda
    @60
    vx
    @1
    rsp
    syl
    @57
    @61
    vx
    @8
    wral
    #
    @59
    @61
    wi
    @0
    @33
    @8
    @13
    wss
    @63
    vx
    vw
    @8
    cB
    ctb
    eltg2
    simplbda
    @61
    vx
    @8
    rsp
    syl
    im2anan9
    @24
    @1
    @8
    elin
    @46
    @50
    vz
    vw
    cB
    cB
    reeanv
    3imtr4g
    anandis
    @0
    @54
    @55
    @0
    @42
    @53
    @38
    @0
    @42
    @53
    @38
    wi
    @0
    @42
    wa
    #
    @52
    @38
    vz
    cB
    @64
    @44
    cB
    wcel
    #
    wa
    #
    @51
    @38
    vw
    cB
    @51
    @66
    @48
    cB
    wcel
    #
    @24
    @44
    @48
    cin
    #
    wcel
    #
    @68
    @9
    wss
    #
    wa
    #
    @38
    @43
    @47
    @45
    @49
    @71
    @43
    @47
    wa
    #
    @69
    @45
    @49
    wa
    @70
    @69
    @72
    @24
    @44
    @48
    elin
    biimpri
    @44
    @1
    @48
    @8
    ss2in
    anim12i
    an4s
    @66
    @67
    @71
    wa
    wa
    @25
    @27
    @68
    wss
    #
    wa
    #
    vt
    cB
    wrex
    #
    @38
    @66
    @67
    @69
    @75
    @70
    @0
    @65
    @67
    @69
    wa
    @75
    @42
    vt
    @24
    cB
    @44
    @48
    basis2
    adantllr
    adantrrr
    @71
    @75
    @38
    wi
    #
    @66
    @67
    @70
    @76
    @69
    @70
    @74
    @37
    vt
    cB
    @70
    @73
    @36
    @25
    @73
    @70
    @36
    @27
    @68
    @9
    sstr2
    com12
    anim2d
    reximdv
    adantl
    ad2antll
    mpd
    sylanr2
    rexlimdvaa
    rexlimdva
    ex
    a2d
    imp
    syldan
    ralrimiv
    jca
    ex
    vx
    vt
    @9
    cB
    ctb
    eltg2
    sylibrd
    ralrimivv
    @2
    cvv
    wcel
    @12
    @7
    @11
    wa
    wb
    cB
    ctg
    fvex
    vu
    vv
    cvv
    @2
    istopg
    ax-mp
    sylanbrc
end
