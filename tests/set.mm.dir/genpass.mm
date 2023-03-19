include "cnp.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "genpelv.mm"
include "3adant1.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "df-rex.mm"
include "ovex.mm"
include "isseti.mm"
include "biantrur.mm"
include "19.41v.mm"
include "bitr4i.mm"
include "rexbii.mm"
include "rexcom4.mm"
include "bitri.mm"
include "oveq2.mm"
include "syl6eqr.mm"
include "eqeq2d.mm"
include "pm5.32i.mm"
include "r19.41v.mm"
include "bitr3i.mm"
include "exbii.mm"
include "3bitri.mm"
include "3bitr4g.mm"
include "rexbidv.mm"
include "caovcl.mm"
include "sylan2.mm"
include "3impb.mm"
include "stoic3.mm"
include "3adant3.mm"
include "oveq1.mm"
include "3bitr4ri.mm"
include "r19.41vv.mm"
include "bitrd.mm"
include "3bitr4rd.mm"
include "eqrdv.mm"
include "0npr.mm"
include "ndmovass.mm"
include "pm2.61i.mm"

theorem genpass
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cF: class F
  let cG: class G
  let vt: setvar t
  let cD: class D
  assume genp.1: |- F = ( w e. P. , v e. P. |-> { x | E. y e. w E. z e. v x = ( y G z ) } )
  assume genp.2: |- ( ( y e. Q. /\ z e. Q. ) -> ( y G z ) e. Q. )
  assume genpass.4: |- dom F = ( P. X. P. )
  assume genpass.5: |- ( ( f e. P. /\ g e. P. ) -> ( f F g ) e. P. )
  assume genpass.6: |- ( ( f G g ) G h ) = ( f G ( g G h ) )

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint f x
  disjoint g x
  disjoint h x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint f y
  disjoint g y
  disjoint h y
  disjoint w z
  disjoint v z
  disjoint f z
  disjoint g z
  disjoint h z
  disjoint v w
  disjoint f w
  disjoint g w
  disjoint h w
  disjoint f v
  disjoint g v
  disjoint h v
  disjoint f g
  disjoint f h
  disjoint g h
  disjoint A x
  disjoint A f
  disjoint A g
  disjoint A h
  disjoint B x
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint F h
  disjoint x y
  disjoint x z
  disjoint f x
  disjoint g x
  disjoint h x
  disjoint A x
  disjoint y z
  disjoint f y
  disjoint g y
  disjoint h y
  disjoint A y
  disjoint f z
  disjoint g z
  disjoint h z
  disjoint A z
  disjoint f g
  disjoint f h
  disjoint A f
  disjoint g h
  disjoint A g
  disjoint A h
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B f
  disjoint B g
  disjoint B h
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
  disjoint f w
  disjoint g w
  disjoint h w
  disjoint G w
  disjoint f v
  disjoint g v
  disjoint h v
  disjoint G v
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint F f
  disjoint F g
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint t w
  disjoint t v
  disjoint f t
  disjoint g t
  disjoint h t
  disjoint A t
  disjoint B t
  disjoint C t
  disjoint F t
  disjoint G t
  disjoint D g
  disjoint D h
  assert |- ( ( A F B ) F C ) = ( A F ( B F C ) )

  proof
    cA
    cnp
    wcel
    #
    cB
    cnp
    wcel
    #
    cC
    cnp
    wcel
    #
    w3a
    #
    cA
    cB
    cF
    co
    #
    cC
    cF
    co
    #
    cA
    cB
    cC
    cF
    co
    #
    cF
    co
    #
    wceq
    @3
    vx
    @5
    @7
    @3
    vx
    cv
    #
    vf
    cv
    #
    vt
    cv
    #
    cG
    co
    #
    wceq
    #
    vt
    @6
    wrex
    #
    vf
    cA
    wrex
    #
    @8
    @9
    vg
    cv
    #
    cG
    co
    #
    vh
    cv
    #
    cG
    co
    #
    wceq
    #
    vh
    cC
    wrex
    #
    vg
    cB
    wrex
    #
    vf
    cA
    wrex
    #
    @8
    @7
    wcel
    #
    @8
    @5
    wcel
    #
    @3
    @13
    @21
    vf
    cA
    @3
    @10
    @6
    wcel
    #
    @12
    wa
    #
    vt
    wex
    @10
    @15
    @17
    cG
    co
    #
    wceq
    #
    vh
    cC
    wrex
    #
    vg
    cB
    wrex
    #
    @12
    wa
    #
    vt
    wex
    #
    @13
    @21
    @3
    @26
    @31
    vt
    @3
    @25
    @30
    @12
    @1
    @2
    @25
    @30
    wb
    @0
    vx
    vy
    vz
    vw
    vv
    cB
    cC
    @10
    vg
    vh
    cF
    cG
    genp.1
    genp.2
    genpelv
    3adant1
    anbi1d
    exbidv
    @12
    vt
    @6
    df-rex
    @21
    @28
    @19
    wa
    #
    vh
    cC
    wrex
    #
    vt
    wex
    #
    vg
    cB
    wrex
    @34
    vg
    cB
    wrex
    #
    vt
    wex
    @32
    @20
    @35
    vg
    cB
    @20
    @33
    vt
    wex
    #
    vh
    cC
    wrex
    @35
    @19
    @37
    vh
    cC
    @19
    @28
    vt
    wex
    #
    @19
    wa
    @37
    @38
    @19
    vt
    @27
    @15
    @17
    cG
    ovex
    isseti
    biantrur
    @28
    @19
    vt
    19.41v
    bitr4i
    rexbii
    @33
    vh
    vt
    cC
    rexcom4
    bitri
    rexbii
    @34
    vg
    vt
    cB
    rexcom4
    @36
    @31
    vt
    @36
    @29
    @12
    wa
    #
    vg
    cB
    wrex
    @31
    @34
    @39
    vg
    cB
    @34
    @28
    @12
    wa
    #
    vh
    cC
    wrex
    @39
    @40
    @33
    vh
    cC
    @28
    @12
    @19
    @28
    @11
    @18
    @8
    @28
    @11
    @9
    @27
    cG
    co
    @18
    @10
    @27
    @9
    cG
    oveq2
    genpass.6
    syl6eqr
    eqeq2d
    pm5.32i
    rexbii
    @28
    @12
    vh
    cC
    r19.41v
    bitr3i
    rexbii
    @29
    @12
    vg
    cB
    r19.41v
    bitri
    exbii
    3bitri
    3bitr4g
    rexbidv
    @0
    @1
    @2
    @23
    @14
    wb
    #
    @1
    @2
    wa
    @0
    @6
    cnp
    wcel
    @41
    vf
    vg
    cB
    cC
    cnp
    cF
    genpass.5
    caovcl
    vx
    vy
    vz
    vw
    vv
    cA
    @6
    @8
    vf
    vt
    cF
    cG
    genp.1
    genp.2
    genpelv
    sylan2
    3impb
    @3
    @24
    @8
    @10
    @17
    cG
    co
    #
    wceq
    #
    vh
    cC
    wrex
    #
    vt
    @4
    wrex
    #
    @22
    @0
    @1
    @4
    cnp
    wcel
    @2
    @24
    @45
    wb
    vf
    vg
    cA
    cB
    cnp
    cF
    genpass.5
    caovcl
    vx
    vy
    vz
    vw
    vv
    @4
    cC
    @8
    vt
    vh
    cF
    cG
    genp.1
    genp.2
    genpelv
    stoic3
    @3
    @10
    @4
    wcel
    #
    @44
    wa
    #
    vt
    wex
    @10
    @16
    wceq
    #
    vg
    cB
    wrex
    vf
    cA
    wrex
    #
    @44
    wa
    #
    vt
    wex
    #
    @45
    @22
    @3
    @47
    @50
    vt
    @3
    @46
    @49
    @44
    @0
    @1
    @46
    @49
    wb
    @2
    vx
    vy
    vz
    vw
    vv
    cA
    cB
    @10
    vf
    vg
    cF
    cG
    genp.1
    genp.2
    genpelv
    3adant3
    anbi1d
    exbidv
    @44
    vt
    @4
    df-rex
    @22
    @48
    @44
    wa
    #
    vg
    cB
    wrex
    #
    vt
    wex
    #
    vf
    cA
    wrex
    @53
    vf
    cA
    wrex
    #
    vt
    wex
    @51
    @21
    @54
    vf
    cA
    @21
    @52
    vt
    wex
    #
    vg
    cB
    wrex
    @54
    @20
    @56
    vg
    cB
    @48
    @20
    wa
    #
    vt
    wex
    @48
    vt
    wex
    #
    @20
    wa
    @56
    @20
    @48
    @20
    vt
    19.41v
    @52
    @57
    vt
    @48
    @44
    @20
    @48
    @43
    @19
    vh
    cC
    @48
    @42
    @18
    @8
    @10
    @16
    @17
    cG
    oveq1
    eqeq2d
    rexbidv
    pm5.32i
    exbii
    @58
    @20
    vt
    @16
    @9
    @15
    cG
    ovex
    isseti
    biantrur
    3bitr4ri
    rexbii
    @52
    vg
    vt
    cB
    rexcom4
    bitri
    rexbii
    @53
    vf
    vt
    cA
    rexcom4
    @55
    @50
    vt
    @48
    @44
    vf
    vg
    cA
    cB
    r19.41vv
    exbii
    3bitri
    3bitr4g
    bitrd
    3bitr4rd
    eqrdv
    cA
    cB
    cC
    cnp
    cF
    genpass.4
    0npr
    ndmovass
    pm2.61i
end
