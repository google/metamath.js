include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "cmv.mm"
include "cph.mm"
include "cin.mm"
include "an4.mm"
include "eqeq1.mm"
include "biimpcd.mm"
include "anim12d.mm"
include "expdcom.mm"
include "imp32.mm"
include "anim2i.mm"
include "an4s.mm"
include "syl2anb.mm"
include "5oalem5.mm"
include "syl.mm"
include "wi.mm"
include "shscli.mm"
include "shincli.mm"
include "5oalem1.mm"
include "expr.mm"
include "adantrr.mm"
include "adantr.mm"
include "mpd.mm"

theorem 5oalem6
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
  let vh: setvar h
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


  assert |- ( ( ( ( ( x e. A /\ y e. B ) /\ h = ( x +h y ) ) /\ ( ( z e. C /\ w e. D ) /\ h = ( z +h w ) ) ) /\ ( ( ( f e. F /\ g e. G ) /\ h = ( f +h g ) ) /\ ( ( v e. R /\ u e. S ) /\ h = ( v +h u ) ) ) ) -> h e. ( B +H ( A i^i ( C +H ( ( ( ( A +H C ) i^i ( B +H D ) ) i^i ( ( ( A +H R ) i^i ( B +H S ) ) +H ( ( C +H R ) i^i ( D +H S ) ) ) ) i^i ( ( ( ( A +H F ) i^i ( B +H G ) ) i^i ( ( ( A +H R ) i^i ( B +H S ) ) +H ( ( F +H R ) i^i ( G +H S ) ) ) ) +H ( ( ( C +H F ) i^i ( D +H G ) ) i^i ( ( ( C +H R ) i^i ( D +H S ) ) +H ( ( F +H R ) i^i ( G +H S ) ) ) ) ) ) ) ) ) )

  proof
    vx
    cv
    #
    cA
    wcel
    vy
    cv
    #
    cB
    wcel
    wa
    #
    vh
    cv
    #
    @0
    @1
    cva
    co
    #
    wceq
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
    @3
    @7
    @9
    cva
    co
    #
    wceq
    #
    wa
    wa
    #
    vf
    cv
    #
    cF
    wcel
    vg
    cv
    #
    cG
    wcel
    wa
    #
    @3
    @15
    @16
    cva
    co
    #
    wceq
    #
    wa
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
    @3
    @20
    @21
    cva
    co
    #
    wceq
    #
    wa
    wa
    #
    wa
    #
    @0
    @7
    cmv
    co
    cA
    cC
    cph
    co
    #
    cB
    cD
    cph
    co
    #
    cin
    #
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
    #
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
    @32
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
    @35
    @43
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
    wcel
    #
    @3
    cB
    cA
    cC
    @52
    cph
    co
    cin
    cph
    co
    wcel
    #
    @26
    @2
    @11
    wa
    #
    @17
    @22
    wa
    #
    wa
    #
    @4
    @23
    wceq
    #
    @12
    @23
    wceq
    #
    wa
    #
    @18
    @23
    wceq
    #
    wa
    #
    wa
    #
    @53
    @14
    @55
    @5
    @13
    wa
    #
    wa
    @56
    @19
    @24
    wa
    #
    wa
    @63
    @25
    @2
    @5
    @11
    @13
    an4
    @17
    @19
    @22
    @24
    an4
    @55
    @56
    @64
    @65
    @63
    @64
    @65
    wa
    @62
    @57
    @64
    @19
    @24
    @62
    @24
    @64
    @19
    @62
    @24
    @64
    @60
    @19
    @61
    @24
    @5
    @58
    @13
    @59
    @5
    @24
    @58
    @3
    @4
    @23
    eqeq1
    biimpcd
    @13
    @24
    @59
    @3
    @12
    @23
    eqeq1
    biimpcd
    anim12d
    @19
    @24
    @61
    @3
    @18
    @23
    eqeq1
    biimpcd
    anim12d
    expdcom
    imp32
    anim2i
    an4s
    syl2anb
    vx
    vy
    vz
    vw
    vv
    vu
    cA
    cB
    cC
    cD
    cR
    cS
    vf
    vg
    cF
    cG
    5oalem5.1
    5oalem5.2
    5oalem5.3
    5oalem5.4
    5oalem5.5
    5oalem5.6
    5oalem5.7
    5oalem5.8
    5oalem5
    syl
    @14
    @53
    @54
    wi
    #
    @25
    @6
    @11
    @66
    @13
    @6
    @8
    @66
    @10
    @6
    @8
    @53
    @54
    vx
    vy
    vz
    vh
    cA
    cB
    cC
    @52
    5oalem5.1
    5oalem5.2
    5oalem5.3
    @37
    @51
    @29
    @36
    @27
    @28
    cA
    cC
    5oalem5.1
    5oalem5.3
    shscli
    cB
    cD
    5oalem5.2
    5oalem5.4
    shscli
    shincli
    @32
    @35
    @30
    @31
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
    #
    @33
    @34
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
    #
    shscli
    shincli
    @45
    @50
    @40
    @44
    @38
    @39
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
    @32
    @43
    @67
    @41
    @42
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
    @48
    @49
    @46
    @47
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
    @35
    @43
    @68
    @69
    shscli
    shincli
    shscli
    shincli
    5oalem1
    expr
    adantrr
    adantrr
    adantr
    mpd
end
