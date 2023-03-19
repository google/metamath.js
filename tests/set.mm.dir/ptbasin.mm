include "wcel.mm"
include "ctop.mm"
include "wf.mm"
include "wa.mm"
include "cin.mm"
include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "wral.mm"
include "cuni.mm"
include "wceq.mm"
include "cdif.mm"
include "cfn.mm"
include "wrex.mm"
include "w3a.mm"
include "cixp.mm"
include "wex.mm"
include "elpt.mm"
include "anbi12i.mm"
include "eeanv.mm"
include "bitr4i.mm"
include "an4.mm"
include "an6.mm"
include "df-3an.mm"
include "bitri.mm"
include "wi.mm"
include "reeanv.mm"
include "fveq2.mm"
include "ineq12d.mm"
include "cbvixpv.mm"
include "cun.mm"
include "simpl1l.mm"
include "unfi.mm"
include "ad2antrl.mm"
include "simpl1r.mm"
include "ffvelrnda.mm"
include "simpl3l.mm"
include "eleq12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "simpl3r.mm"
include "inopn.mm"
include "syl3anc.mm"
include "simprrl.mm"
include "wss.mm"
include "ssun1.mm"
include "sscon.mm"
include "ax-mp.mm"
include "sseli.mm"
include "unieqd.mm"
include "eqeq12d.mm"
include "syl2an.mm"
include "simprrr.mm"
include "ssun2.mm"
include "inidm.mm"
include "syl6eq.mm"
include "elptr2.mm"
include "syl5eqel.mm"
include "expr.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "3expb.mm"
include "impr.mm"
include "sylan2b.mm"
include "ineq12.mm"
include "ixpin.mm"
include "syl6eqr.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "exlimdvv.mm"
include "imp.mm"

theorem ptbasin
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vg: setvar g
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vk: setvar k
  let vn: setvar n
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vh: setvar h
  let vw: setvar w
  let cG: class G
  let cI: class I
  let wph: wff ph
  let vm: setvar m
  let cU: class U
  let cS: class S
  let cW: class W
  assume ptbas.1: |- B = { x | E. g ( ( g Fn A /\ A. y e. A ( g ` y ) e. ( F ` y ) /\ E. z e. Fin A. y e. ( A \ z ) ( g ` y ) = U. ( F ` y ) ) /\ x = X_ y e. A ( g ` y ) ) }

  disjoint g x
  disjoint g y
  disjoint x y
  disjoint g z
  disjoint A g
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint Y g
  disjoint Y x
  disjoint F g
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint X g
  disjoint X x
  disjoint X z
  disjoint V g
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a k
  disjoint a n
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint B a
  disjoint b c
  disjoint b d
  disjoint b k
  disjoint b n
  disjoint b s
  disjoint b u
  disjoint b v
  disjoint B b
  disjoint c d
  disjoint c k
  disjoint c n
  disjoint c s
  disjoint c u
  disjoint c v
  disjoint B c
  disjoint d k
  disjoint d n
  disjoint d s
  disjoint d u
  disjoint d v
  disjoint B d
  disjoint k n
  disjoint k s
  disjoint k u
  disjoint k v
  disjoint B k
  disjoint n s
  disjoint n u
  disjoint n v
  disjoint B n
  disjoint s u
  disjoint s v
  disjoint B s
  disjoint u v
  disjoint B u
  disjoint B v
  disjoint g h
  disjoint g w
  disjoint G g
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint G h
  disjoint w x
  disjoint w y
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint g n
  disjoint I g
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint I n
  disjoint I w
  disjoint I x
  disjoint I y
  disjoint k ph
  disjoint a g
  disjoint a h
  disjoint a m
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b g
  disjoint b h
  disjoint b m
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint c g
  disjoint c h
  disjoint c m
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint A c
  disjoint d g
  disjoint d h
  disjoint d m
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint A d
  disjoint g k
  disjoint g m
  disjoint g s
  disjoint g u
  disjoint g v
  disjoint h k
  disjoint h m
  disjoint h n
  disjoint h s
  disjoint h u
  disjoint h v
  disjoint h z
  disjoint A h
  disjoint k m
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint m n
  disjoint m s
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n z
  disjoint A n
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w z
  disjoint A w
  disjoint U g
  disjoint U n
  disjoint U w
  disjoint U x
  disjoint U y
  disjoint Y a
  disjoint Y b
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F h
  disjoint F k
  disjoint F m
  disjoint F n
  disjoint F s
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint X a
  disjoint X b
  disjoint X h
  disjoint X k
  disjoint X m
  disjoint X s
  disjoint X u
  disjoint X w
  disjoint S g
  disjoint S h
  disjoint S x
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V d
  disjoint V h
  disjoint V k
  disjoint V m
  disjoint V n
  disjoint V s
  disjoint V u
  disjoint V v
  disjoint V w
  disjoint W k
  disjoint W w
  disjoint W y
  assert |- ( ( ( A e. V /\ F : A --> Top ) /\ ( X e. B /\ Y e. B ) ) -> ( X i^i Y ) e. B )

  proof
    cA
    cV
    wcel
    #
    cA
    ctop
    cF
    wf
    #
    wa
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cX
    cY
    cin
    #
    cB
    wcel
    #
    @5
    va
    cv
    #
    cA
    wfn
    #
    vy
    cv
    #
    @8
    cfv
    #
    @10
    cF
    cfv
    #
    wcel
    #
    vy
    cA
    wral
    #
    @11
    @12
    cuni
    #
    wceq
    #
    vy
    cA
    vc
    cv
    #
    cdif
    #
    wral
    #
    vc
    cfn
    wrex
    #
    w3a
    #
    cX
    vy
    cA
    @11
    cixp
    #
    wceq
    #
    wa
    #
    vb
    cv
    #
    cA
    wfn
    #
    @10
    @25
    cfv
    #
    @12
    wcel
    #
    vy
    cA
    wral
    #
    @27
    @15
    wceq
    #
    vy
    cA
    vd
    cv
    #
    cdif
    #
    wral
    #
    vd
    cfn
    wrex
    #
    w3a
    #
    cY
    vy
    cA
    @27
    cixp
    #
    wceq
    #
    wa
    #
    wa
    #
    vb
    wex
    va
    wex
    #
    @2
    @7
    @5
    @24
    va
    wex
    #
    @38
    vb
    wex
    #
    wa
    @40
    @3
    @41
    @4
    @42
    vx
    vy
    vz
    vc
    cA
    cB
    cX
    vg
    va
    cF
    ptbas.1
    elpt
    vx
    vy
    vz
    vd
    cA
    cB
    cY
    vg
    vb
    cF
    ptbas.1
    elpt
    anbi12i
    @24
    @38
    va
    vb
    eeanv
    bitr4i
    @2
    @39
    @7
    va
    vb
    @39
    @21
    @35
    wa
    #
    @23
    @37
    wa
    #
    wa
    @2
    @7
    @21
    @23
    @35
    @37
    an4
    @2
    @43
    @44
    @7
    @2
    @43
    wa
    @7
    @44
    vy
    cA
    @11
    @27
    cin
    #
    cixp
    #
    cB
    wcel
    #
    @43
    @2
    @9
    @26
    wa
    #
    @14
    @29
    wa
    #
    wa
    #
    @20
    @34
    wa
    #
    wa
    #
    @47
    @43
    @48
    @49
    @51
    w3a
    @52
    @9
    @14
    @20
    @26
    @29
    @34
    an6
    @48
    @49
    @51
    df-3an
    bitri
    @2
    @50
    @51
    @47
    @2
    @48
    @49
    @51
    @47
    wi
    @51
    @19
    @33
    wa
    #
    vd
    cfn
    wrex
    vc
    cfn
    wrex
    @2
    @48
    @49
    w3a
    #
    @47
    @19
    @33
    vc
    vd
    cfn
    cfn
    reeanv
    @54
    @53
    @47
    vc
    vd
    cfn
    cfn
    @54
    @17
    cfn
    wcel
    @31
    cfn
    wcel
    wa
    #
    @53
    @47
    @54
    @55
    @53
    wa
    #
    wa
    #
    @46
    vk
    cA
    vk
    cv
    #
    @8
    cfv
    #
    @58
    @25
    cfv
    #
    cin
    #
    cixp
    cB
    vy
    vk
    cA
    @45
    @61
    @10
    @58
    wceq
    #
    @11
    @59
    @27
    @60
    @10
    @58
    @8
    fveq2
    #
    @10
    @58
    @25
    fveq2
    #
    ineq12d
    cbvixpv
    @57
    vx
    vy
    vz
    cA
    cB
    @61
    vg
    vk
    cF
    cV
    @17
    @31
    cun
    #
    ptbas.1
    @0
    @1
    @48
    @49
    @56
    simpl1l
    @55
    @65
    cfn
    wcel
    @54
    @53
    @17
    @31
    unfi
    ad2antrl
    @57
    @58
    cA
    wcel
    #
    wa
    @58
    cF
    cfv
    #
    ctop
    wcel
    @59
    @67
    wcel
    #
    @60
    @67
    wcel
    #
    @61
    @67
    wcel
    @57
    cA
    ctop
    @58
    cF
    @0
    @1
    @48
    @49
    @56
    simpl1r
    ffvelrnda
    @57
    @14
    @66
    @68
    @14
    @29
    @2
    @48
    @56
    simpl3l
    @13
    @68
    vy
    @58
    cA
    @62
    @11
    @59
    @12
    @67
    @63
    @10
    @58
    cF
    fveq2
    #
    eleq12d
    rspccva
    sylan
    @57
    @29
    @66
    @69
    @14
    @29
    @2
    @48
    @56
    simpl3r
    @28
    @69
    vy
    @58
    cA
    @62
    @27
    @60
    @12
    @67
    @64
    @70
    eleq12d
    rspccva
    sylan
    @59
    @60
    @67
    inopn
    syl3anc
    @57
    @58
    cA
    @65
    cdif
    #
    wcel
    #
    wa
    #
    @61
    @67
    cuni
    #
    @74
    cin
    @74
    @73
    @59
    @74
    @60
    @74
    @57
    @19
    @58
    @18
    wcel
    @59
    @74
    wceq
    #
    @72
    @54
    @55
    @19
    @33
    simprrl
    @71
    @18
    @58
    @17
    @65
    wss
    @71
    @18
    wss
    @17
    @31
    ssun1
    @17
    @65
    cA
    sscon
    ax-mp
    sseli
    @16
    @75
    vy
    @58
    @18
    @62
    @11
    @59
    @15
    @74
    @63
    @62
    @12
    @67
    @70
    unieqd
    #
    eqeq12d
    rspccva
    syl2an
    @57
    @33
    @58
    @32
    wcel
    @60
    @74
    wceq
    #
    @72
    @54
    @55
    @19
    @33
    simprrr
    @71
    @32
    @58
    @31
    @65
    wss
    @71
    @32
    wss
    @31
    @17
    ssun2
    @31
    @65
    cA
    sscon
    ax-mp
    sseli
    @30
    @77
    vy
    @58
    @32
    @62
    @27
    @60
    @15
    @74
    @64
    @76
    eqeq12d
    rspccva
    syl2an
    ineq12d
    @74
    inidm
    syl6eq
    elptr2
    syl5eqel
    expr
    rexlimdvva
    syl5bir
    3expb
    impr
    sylan2b
    @44
    @6
    @46
    cB
    @44
    @6
    @22
    @36
    cin
    @46
    cX
    @22
    cY
    @36
    ineq12
    vy
    cA
    @11
    @27
    ixpin
    syl6eqr
    eleq1d
    syl5ibrcom
    expimpd
    syl5bi
    exlimdvv
    syl5bi
    imp
end
