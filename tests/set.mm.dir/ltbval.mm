include "cltb.mm"
include "co.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "copab.mm"
include "wcel.mm"
include "cvv.mm"
include "elex.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "crab.mm"
include "simpr.mm"
include "oveq2d.mm"
include "rabeq.mm"
include "syl.mm"
include "syl6eqr.mm"
include "sseq2d.mm"
include "simpl.mm"
include "breqd.mm"
include "imbi1d.mm"
include "raleqbidv.mm"
include "anbi2d.mm"
include "rexeqbidv.mm"
include "anbi12d.mm"
include "opabbidv.mm"
include "df-ltbag.mm"
include "vex.mm"
include "prss.mm"
include "anbi1i.mm"
include "opabbii.mm"
include "cxp.mm"
include "ovex.mm"
include "rabex2.mm"
include "xpex.mm"
include "opabssxp.mm"
include "ssexi.mm"
include "eqeltrri.mm"
include "ovmpt2a.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "syl5eq.mm"

theorem ltbval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cC: class C
  let cD: class D
  let cT: class T
  let vh: setvar h
  let cI: class I
  let cV: class V
  let cW: class W
  let vi: setvar i
  let vr: setvar r
  assume ltbval.c: |- C = ( T <bag I )
  assume ltbval.d: |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin }
  assume ltbval.i: |- ( ph -> I e. V )
  assume ltbval.t: |- ( ph -> T e. W )

  disjoint x y
  disjoint D x
  disjoint D y
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint I h
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint I w
  disjoint x z
  disjoint I x
  disjoint y z
  disjoint I y
  disjoint I z
  disjoint h ph
  disjoint ph x
  disjoint ph y
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint i r
  disjoint i x
  disjoint i y
  disjoint D i
  disjoint r x
  disjoint r y
  disjoint D r
  disjoint h i
  disjoint h r
  disjoint i w
  disjoint i z
  disjoint I i
  disjoint r w
  disjoint r z
  disjoint I r
  disjoint T i
  disjoint T r
  assert |- ( ph -> C = { <. x , y >. | ( { x , y } C_ D /\ E. z e. I ( ( x ` z ) < ( y ` z ) /\ A. w e. I ( z T w -> ( x ` w ) = ( y ` w ) ) ) ) } )

  proof
    wph
    cC
    cT
    cI
    cltb
    co
    #
    vx
    cv
    #
    vy
    cv
    #
    cpr
    #
    cD
    wss
    #
    vz
    cv
    #
    @1
    cfv
    @5
    @2
    cfv
    clt
    wbr
    #
    @5
    vw
    cv
    #
    cT
    wbr
    #
    @7
    @1
    cfv
    @7
    @2
    cfv
    wceq
    #
    wi
    #
    vw
    cI
    wral
    #
    wa
    #
    vz
    cI
    wrex
    #
    wa
    #
    vx
    vy
    copab
    #
    ltbval.c
    wph
    cT
    cW
    wcel
    #
    cI
    cV
    wcel
    #
    @0
    @15
    wceq
    #
    ltbval.t
    ltbval.i
    @16
    cT
    cvv
    wcel
    cI
    cvv
    wcel
    @18
    @17
    cT
    cW
    elex
    cI
    cV
    elex
    vr
    vi
    cT
    cI
    cvv
    cvv
    @3
    vh
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    #
    vh
    cn0
    vi
    cv
    #
    cmap
    co
    #
    crab
    #
    wss
    #
    @6
    @5
    @7
    vr
    cv
    #
    wbr
    #
    @9
    wi
    #
    vw
    @20
    wral
    #
    wa
    #
    vz
    @20
    wrex
    #
    wa
    #
    vx
    vy
    copab
    @15
    cltb
    @24
    cT
    wceq
    #
    @20
    cI
    wceq
    #
    wa
    #
    @30
    @14
    vx
    vy
    @33
    @23
    @4
    @29
    @13
    @33
    @22
    cD
    @3
    @33
    @22
    @19
    vh
    cn0
    cI
    cmap
    co
    #
    crab
    #
    cD
    @33
    @21
    @34
    wceq
    @22
    @35
    wceq
    @33
    @20
    cI
    cn0
    cmap
    @31
    @32
    simpr
    #
    oveq2d
    @19
    vh
    @21
    @34
    rabeq
    syl
    ltbval.d
    syl6eqr
    sseq2d
    @33
    @28
    @12
    vz
    @20
    cI
    @36
    @33
    @27
    @11
    @6
    @33
    @26
    @10
    vw
    @20
    cI
    @36
    @33
    @25
    @8
    @9
    @33
    @24
    cT
    @5
    @7
    @31
    @32
    simpl
    breqd
    imbi1d
    raleqbidv
    anbi2d
    rexeqbidv
    anbi12d
    opabbidv
    vx
    vy
    vz
    vw
    vh
    vi
    vr
    df-ltbag
    @1
    cD
    wcel
    @2
    cD
    wcel
    wa
    #
    @13
    wa
    #
    vx
    vy
    copab
    #
    @15
    cvv
    @38
    @14
    vx
    vy
    @37
    @4
    @13
    @1
    @2
    cD
    vx
    vex
    vy
    vex
    prss
    anbi1i
    opabbii
    @39
    cD
    cD
    cxp
    cD
    cD
    @19
    vh
    @34
    cD
    ltbval.d
    cn0
    cI
    cmap
    ovex
    rabex2
    #
    @40
    xpex
    @13
    vx
    vy
    cD
    cD
    opabssxp
    ssexi
    eqeltrri
    ovmpt2a
    syl2an
    syl2anc
    syl5eq
end
