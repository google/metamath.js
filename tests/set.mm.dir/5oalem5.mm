include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "cph.mm"
include "cin.mm"
include "cmv.mm"
include "simpr.mm"
include "anim2i.mm"
include "simpl.mm"
include "5oalem4.mm"
include "syl2an.mm"
include "chil.mm"
include "sheli.mm"
include "adantr.mm"
include "anim12i.mm"
include "hvsubsub4.mm"
include "anandirs.mm"
include "c0v.mm"
include "hvsubid.mm"
include "oveq2d.mm"
include "hvsubcl.mm"
include "hvsub0.mm"
include "syl.mm"
include "sylan9eqr.mm"
include "eqtrd.mm"
include "adantrr.mm"
include "anandir.mm"
include "sylib.mm"
include "simprr.mm"
include "jca.mm"
include "anim1i.mm"
include "an4s.mm"
include "sylanb.mm"
include "shscli.mm"
include "shincli.mm"
include "shsvsi.mm"
include "eqeltrrd.mm"
include "elind.mm"

theorem 5oalem5
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cG: class G
  assume 5oalem5.1: |- A e. SH
  assume 5oalem5.2: |- B e. SH
  assume 5oalem5.3: |- C e. SH
  assume 5oalem5.4: |- D e. SH
  assume 5oalem5.5: |- F e. SH
  assume 5oalem5.6: |- G e. SH
  assume 5oalem5.7: |- R e. SH
  assume 5oalem5.8: |- S e. SH


  assert |- ( ( ( ( ( x e. A /\ y e. B ) /\ ( z e. C /\ w e. D ) ) /\ ( ( f e. F /\ g e. G ) /\ ( v e. R /\ u e. S ) ) ) /\ ( ( ( x +h y ) = ( v +h u ) /\ ( z +h w ) = ( v +h u ) ) /\ ( f +h g ) = ( v +h u ) ) ) -> ( x -h z ) e. ( ( ( ( A +H C ) i^i ( B +H D ) ) i^i ( ( ( A +H R ) i^i ( B +H S ) ) +H ( ( C +H R ) i^i ( D +H S ) ) ) ) i^i ( ( ( ( A +H F ) i^i ( B +H G ) ) i^i ( ( ( A +H R ) i^i ( B +H S ) ) +H ( ( F +H R ) i^i ( G +H S ) ) ) ) +H ( ( ( C +H F ) i^i ( D +H G ) ) i^i ( ( ( C +H R ) i^i ( D +H S ) ) +H ( ( F +H R ) i^i ( G +H S ) ) ) ) ) ) )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    vz
    cv
    #
    cC
    wcel
    #
    vw
    cv
    #
    cD
    wcel
    #
    wa
    #
    wa
    #
    vf
    cv
    #
    cF
    wcel
    #
    vg
    cv
    #
    cG
    wcel
    #
    wa
    #
    vv
    cv
    #
    cR
    wcel
    vu
    cv
    #
    cS
    wcel
    wa
    #
    wa
    #
    wa
    #
    @0
    @2
    cva
    co
    @16
    @17
    cva
    co
    #
    wceq
    #
    @5
    @7
    cva
    co
    @21
    wceq
    #
    wa
    #
    @11
    @13
    cva
    co
    @21
    wceq
    #
    wa
    #
    wa
    #
    cA
    cC
    cph
    co
    cB
    cD
    cph
    co
    cin
    cA
    cR
    cph
    co
    #
    cB
    cS
    cph
    co
    #
    cin
    #
    cC
    cR
    cph
    co
    #
    cD
    cS
    cph
    co
    #
    cin
    #
    cph
    co
    cin
    #
    cA
    cF
    cph
    co
    #
    cB
    cG
    cph
    co
    #
    cin
    #
    @30
    cF
    cR
    cph
    co
    #
    cG
    cS
    cph
    co
    #
    cin
    #
    cph
    co
    #
    cin
    #
    cC
    cF
    cph
    co
    #
    cD
    cG
    cph
    co
    #
    cin
    #
    @33
    @40
    cph
    co
    #
    cin
    #
    cph
    co
    #
    @0
    @5
    cmv
    co
    #
    @20
    @10
    @18
    wa
    @24
    @49
    @34
    wcel
    @26
    @19
    @18
    @10
    @15
    @18
    simpr
    anim2i
    @24
    @25
    simpl
    vx
    vy
    vz
    vw
    cA
    cB
    cC
    cD
    vv
    vu
    cR
    cS
    5oalem5.1
    5oalem5.2
    5oalem5.3
    5oalem5.4
    5oalem5.7
    5oalem5.8
    5oalem4
    syl2an
    @27
    @0
    @11
    cmv
    co
    #
    @5
    @11
    cmv
    co
    #
    cmv
    co
    #
    @49
    @48
    @20
    @52
    @49
    wceq
    #
    @26
    @10
    @15
    @53
    @18
    @10
    @0
    chil
    wcel
    #
    @5
    chil
    wcel
    #
    wa
    #
    @11
    chil
    wcel
    #
    @53
    @15
    @4
    @54
    @9
    @55
    @1
    @54
    @3
    @0
    cA
    5oalem5.1
    sheli
    adantr
    @6
    @55
    @8
    @5
    cC
    5oalem5.3
    sheli
    adantr
    anim12i
    @12
    @57
    @14
    @11
    cF
    5oalem5.5
    sheli
    adantr
    @56
    @57
    wa
    @52
    @49
    @11
    @11
    cmv
    co
    #
    cmv
    co
    #
    @49
    @54
    @55
    @57
    @52
    @59
    wceq
    @0
    @11
    @5
    @11
    hvsubsub4
    anandirs
    @57
    @56
    @59
    @49
    c0v
    cmv
    co
    #
    @49
    @57
    @58
    c0v
    @49
    cmv
    @11
    hvsubid
    oveq2d
    @56
    @49
    chil
    wcel
    @60
    @49
    wceq
    @0
    @5
    hvsubcl
    @49
    hvsub0
    syl
    sylan9eqr
    eqtrd
    syl2an
    adantrr
    adantr
    @27
    @50
    @42
    wcel
    #
    @51
    @47
    wcel
    #
    wa
    #
    @52
    @48
    wcel
    @20
    @4
    @15
    wa
    #
    @9
    @15
    wa
    #
    wa
    #
    @18
    wa
    #
    @22
    @25
    wa
    #
    @23
    @25
    wa
    #
    wa
    #
    @63
    @26
    @20
    @66
    @18
    @20
    @10
    @15
    wa
    @66
    @19
    @15
    @10
    @15
    @18
    simpl
    anim2i
    @4
    @9
    @15
    anandir
    sylib
    @10
    @15
    @18
    simprr
    jca
    @26
    @68
    @69
    @24
    @22
    @25
    @22
    @23
    simpl
    anim1i
    @24
    @23
    @25
    @22
    @23
    simpr
    anim1i
    jca
    @67
    @64
    @18
    wa
    #
    @65
    @18
    wa
    #
    wa
    @70
    @63
    @64
    @65
    @18
    anandir
    @71
    @68
    @72
    @69
    @63
    @71
    @68
    wa
    @61
    @72
    @69
    wa
    @62
    vx
    vy
    vf
    vg
    cA
    cB
    cF
    cG
    vv
    vu
    cR
    cS
    5oalem5.1
    5oalem5.2
    5oalem5.5
    5oalem5.6
    5oalem5.7
    5oalem5.8
    5oalem4
    vz
    vw
    vf
    vg
    cC
    cD
    cF
    cG
    vv
    vu
    cR
    cS
    5oalem5.3
    5oalem5.4
    5oalem5.5
    5oalem5.6
    5oalem5.7
    5oalem5.8
    5oalem4
    anim12i
    an4s
    sylanb
    syl2an
    @42
    @47
    @50
    @51
    @37
    @41
    @35
    @36
    cA
    cF
    5oalem5.1
    5oalem5.5
    shscli
    cB
    cG
    5oalem5.2
    5oalem5.6
    shscli
    shincli
    @30
    @40
    @28
    @29
    cA
    cR
    5oalem5.1
    5oalem5.7
    shscli
    cB
    cS
    5oalem5.2
    5oalem5.8
    shscli
    shincli
    @38
    @39
    cF
    cR
    5oalem5.5
    5oalem5.7
    shscli
    cG
    cS
    5oalem5.6
    5oalem5.8
    shscli
    shincli
    #
    shscli
    shincli
    @45
    @46
    @43
    @44
    cC
    cF
    5oalem5.3
    5oalem5.5
    shscli
    cD
    cG
    5oalem5.4
    5oalem5.6
    shscli
    shincli
    @33
    @40
    @31
    @32
    cC
    cR
    5oalem5.3
    5oalem5.7
    shscli
    cD
    cS
    5oalem5.4
    5oalem5.8
    shscli
    shincli
    @73
    shscli
    shincli
    shsvsi
    syl
    eqeltrrd
    elind
end
