include "cnp.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cnq.mm"
include "wn.mm"
include "wex.mm"
include "co.mm"
include "wceq.mm"
include "wpss.mm"
include "prpssnq.mm"
include "pssnel.mm"
include "syl.mm"
include "anim12i.mm"
include "eeanv.mm"
include "sylibr.mm"
include "wi.mm"
include "wrex.mm"
include "wral.mm"
include "cltq.mm"
include "wbr.mm"
include "prub.mm"
include "im2anan9.mm"
include "elprnq.mm"
include "anim1i.mm"
include "wor.mm"
include "ltsonq.mm"
include "so2nr.mm"
include "mpan.mm"
include "ad2antrr.mm"
include "wb.mm"
include "simpr.mm"
include "simpl.mm"
include "ancoms.mm"
include "vex.mm"
include "caovord3.mm"
include "anbi2d.mm"
include "sylan.mm"
include "mtbid.mm"
include "ex.mm"
include "con2d.mm"
include "syl2an.mm"
include "syld.mm"
include "an4s.mm"
include "com24.mm"
include "imp32.mm"
include "ralrimivv.mm"
include "ralnex.mm"
include "ralbii.mm"
include "bitri.mm"
include "sylib.mm"
include "genpelv.mm"
include "adantr.mm"
include "mtbird.mm"
include "expcom.mm"
include "caovcl.mm"
include "eleq2.mm"
include "biimprcd.mm"
include "con3d.mm"
include "ad2ant2r.mm"
include "syldc.mm"
include "exlimdvv.mm"
include "mpd.mm"

theorem genpnnp
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cC: class C
  let cD: class D
  assume genp.1: |- F = ( w e. P. , v e. P. |-> { x | E. y e. w E. z e. v x = ( y G z ) } )
  assume genp.2: |- ( ( y e. Q. /\ z e. Q. ) -> ( y G z ) e. Q. )
  assume genpnnp.3: |- ( z e. Q. -> ( x <Q y <-> ( z G x ) <Q ( z G y ) ) )
  assume genpnnp.4: |- ( x G y ) = ( y G x )

  disjoint v w
  disjoint A w
  disjoint A v
  disjoint B w
  disjoint B v
  disjoint F w
  disjoint F v
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint w x
  disjoint v x
  disjoint G x
  disjoint w y
  disjoint v y
  disjoint G y
  disjoint w z
  disjoint v z
  disjoint G z
  disjoint v w
  disjoint G w
  disjoint G v
  disjoint f x
  disjoint g x
  disjoint h x
  disjoint f y
  disjoint g y
  disjoint h y
  disjoint f z
  disjoint g z
  disjoint h z
  disjoint f g
  disjoint f h
  disjoint A f
  disjoint g h
  disjoint A g
  disjoint A h
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint f w
  disjoint g w
  disjoint h w
  disjoint f v
  disjoint g v
  disjoint h v
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint F f
  disjoint F g
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint D g
  disjoint D h
  assert |- ( ( A e. P. /\ B e. P. ) -> -. ( A F B ) = Q. )

  proof
    cA
    cnp
    wcel
    #
    cB
    cnp
    wcel
    #
    wa
    #
    vw
    cv
    #
    cnq
    wcel
    #
    @3
    cA
    wcel
    wn
    #
    wa
    #
    vv
    cv
    #
    cnq
    wcel
    #
    @7
    cB
    wcel
    wn
    #
    wa
    #
    wa
    #
    vv
    wex
    vw
    wex
    #
    cA
    cB
    cF
    co
    #
    cnq
    wceq
    #
    wn
    #
    @2
    @6
    vw
    wex
    #
    @10
    vv
    wex
    #
    wa
    @12
    @0
    @16
    @1
    @17
    @0
    cA
    cnq
    wpss
    @16
    cA
    prpssnq
    vw
    cA
    cnq
    pssnel
    syl
    @1
    cB
    cnq
    wpss
    @17
    cB
    prpssnq
    vv
    cB
    cnq
    pssnel
    syl
    anim12i
    @6
    @10
    vw
    vv
    eeanv
    sylibr
    @2
    @11
    @15
    vw
    vv
    @11
    @2
    @3
    @7
    cG
    co
    #
    @13
    wcel
    #
    wn
    #
    @15
    @4
    @8
    @5
    @9
    @2
    @20
    wi
    #
    @5
    @9
    wa
    #
    @4
    @8
    wa
    #
    @21
    @2
    @22
    @23
    wa
    #
    @20
    @2
    @24
    wa
    #
    @19
    @18
    vf
    cv
    #
    vg
    cv
    #
    cG
    co
    wceq
    #
    vg
    cB
    wrex
    #
    vf
    cA
    wrex
    #
    @25
    @28
    wn
    #
    vg
    cB
    wral
    #
    vf
    cA
    wral
    #
    @30
    wn
    #
    @25
    @31
    vf
    vg
    cA
    cB
    @2
    @22
    @23
    @26
    cA
    wcel
    #
    @27
    cB
    wcel
    #
    wa
    #
    @31
    wi
    @2
    @37
    @23
    @22
    @31
    @2
    @37
    @23
    @22
    @31
    wi
    #
    wi
    #
    @0
    @35
    @1
    @36
    @39
    @0
    @35
    wa
    #
    @1
    @36
    wa
    #
    wa
    @23
    @38
    @40
    @4
    @41
    @8
    @38
    @40
    @4
    wa
    #
    @41
    @8
    wa
    #
    wa
    @22
    @26
    @3
    cltq
    wbr
    #
    @27
    @7
    cltq
    wbr
    #
    wa
    #
    @31
    @42
    @5
    @44
    @43
    @9
    @45
    cA
    @26
    @3
    prub
    cB
    @27
    @7
    prub
    im2anan9
    @42
    @26
    cnq
    wcel
    #
    @4
    wa
    #
    @27
    cnq
    wcel
    #
    @8
    wa
    #
    @46
    @31
    wi
    @43
    @40
    @47
    @4
    cA
    @26
    elprnq
    anim1i
    @41
    @49
    @8
    cB
    @27
    elprnq
    anim1i
    @48
    @50
    wa
    #
    @28
    @46
    @51
    @28
    @46
    wn
    @51
    @28
    wa
    @44
    @3
    @26
    cltq
    wbr
    #
    wa
    #
    @46
    @48
    @53
    wn
    #
    @50
    @28
    cnq
    cltq
    wor
    @48
    @54
    ltsonq
    cnq
    @26
    @3
    cltq
    so2nr
    mpan
    ad2antrr
    @51
    @8
    @47
    wa
    #
    @28
    @53
    @46
    wb
    @50
    @48
    @55
    @50
    @8
    @48
    @47
    @49
    @8
    simpr
    @47
    @4
    simpl
    anim12i
    ancoms
    @55
    @28
    wa
    @52
    @45
    @44
    vx
    vy
    vz
    @3
    @7
    @26
    @27
    cltq
    cnq
    cG
    vw
    vex
    vv
    vex
    genpnnp.3
    vf
    vex
    genpnnp.4
    vg
    vex
    caovord3
    anbi2d
    sylan
    mtbid
    ex
    con2d
    syl2an
    syld
    an4s
    ex
    an4s
    ex
    com24
    imp32
    ralrimivv
    @33
    @29
    wn
    #
    vf
    cA
    wral
    @34
    @32
    @56
    vf
    cA
    @28
    vg
    cB
    ralnex
    ralbii
    @29
    vf
    cA
    ralnex
    bitri
    sylib
    @2
    @19
    @30
    wb
    @24
    vx
    vy
    vz
    vw
    vv
    cA
    cB
    @18
    vf
    vg
    cF
    cG
    genp.1
    genp.2
    genpelv
    adantr
    mtbird
    expcom
    ancoms
    an4s
    @4
    @8
    @20
    @15
    wi
    #
    @5
    @9
    @23
    @18
    cnq
    wcel
    #
    @57
    vy
    vz
    @3
    @7
    cnq
    cG
    genp.2
    caovcl
    @58
    @14
    @19
    @14
    @19
    @58
    @13
    cnq
    @18
    eleq2
    biimprcd
    con3d
    syl
    ad2ant2r
    syldc
    exlimdvv
    mpd
end
