include "cxp.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "co.mm"
include "wex.mm"
include "copab.mm"
include "opabssxp.mm"
include "eqsstri.mm"
include "brel.mm"
include "simpld.mm"
include "anim12i.mm"
include "3anass.mm"
include "sylibr.mm"
include "wi.mm"
include "eqid.mm"
include "breq1.mm"
include "anbi1d.mm"
include "imbi12d.mm"
include "breq2.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "anbi2d.mm"
include "wb.mm"
include "ecopoveq.mm"
include "3adant3.mm"
include "3adant1.mm"
include "oveq12.mm"
include "vex.mm"
include "caov411.mm"
include "caov4.mm"
include "eqtr3i.mm"
include "3eqtr4g.mm"
include "syl6bi.mm"
include "caovcl.mm"
include "ovex.mm"
include "caovcan.mm"
include "syl2an.mm"
include "3impb.mm"
include "3com12.mm"
include "3adant3l.mm"
include "3adant1r.mm"
include "syld.mm"
include "3adant2.mm"
include "sylibrd.mm"
include "3optocl.mm"
include "mpcom.mm"

theorem ecopovtrn
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let c.pl: class .+
  let c.sm: class .~
  let cS: class S
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vt: setvar t
  let vs: setvar s
  let vr: setvar r
  let cD: class D
  assume ecopopr.1: |- .~ = { <. x , y >. | ( ( x e. ( S X. S ) /\ y e. ( S X. S ) ) /\ E. z E. w E. v E. u ( ( x = <. z , w >. /\ y = <. v , u >. ) /\ ( z .+ u ) = ( w .+ v ) ) ) }
  assume ecopopr.com: |- ( x .+ y ) = ( y .+ x )
  assume ecopopr.cl: |- ( ( x e. S /\ y e. S ) -> ( x .+ y ) e. S )
  assume ecopopr.ass: |- ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) )
  assume ecopopr.can: |- ( ( x e. S /\ y e. S ) -> ( ( x .+ y ) = ( x .+ z ) -> y = z ) )

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint .+ x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint .+ y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint .+ z
  disjoint v w
  disjoint u w
  disjoint .+ w
  disjoint u v
  disjoint .+ v
  disjoint .+ u
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint S w
  disjoint S v
  disjoint S u
  disjoint f g
  disjoint f h
  disjoint f t
  disjoint f s
  disjoint f r
  disjoint A f
  disjoint g h
  disjoint g t
  disjoint g s
  disjoint g r
  disjoint A g
  disjoint h t
  disjoint h s
  disjoint h r
  disjoint A h
  disjoint s t
  disjoint r t
  disjoint A t
  disjoint r s
  disjoint A s
  disjoint A r
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint B t
  disjoint B s
  disjoint B r
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint C t
  disjoint C s
  disjoint C r
  disjoint D f
  disjoint D g
  disjoint D h
  disjoint D t
  disjoint D s
  disjoint D r
  disjoint f x
  disjoint g x
  disjoint h x
  disjoint t x
  disjoint s x
  disjoint r x
  disjoint f y
  disjoint g y
  disjoint h y
  disjoint t y
  disjoint s y
  disjoint r y
  disjoint f z
  disjoint g z
  disjoint h z
  disjoint t z
  disjoint s z
  disjoint r z
  disjoint f w
  disjoint g w
  disjoint h w
  disjoint t w
  disjoint s w
  disjoint r w
  disjoint f v
  disjoint g v
  disjoint h v
  disjoint t v
  disjoint s v
  disjoint r v
  disjoint f u
  disjoint g u
  disjoint h u
  disjoint t u
  disjoint s u
  disjoint r u
  disjoint .+ f
  disjoint .+ g
  disjoint .+ h
  disjoint .+ t
  disjoint .+ s
  disjoint .+ r
  disjoint .~ f
  disjoint .~ g
  disjoint .~ h
  disjoint .~ t
  disjoint .~ s
  disjoint .~ r
  disjoint S f
  disjoint S g
  disjoint S h
  disjoint S t
  disjoint S s
  disjoint S r
  assert |- ( ( A .~ B /\ B .~ C ) -> A .~ C )

  proof
    cA
    cS
    cS
    cxp
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cC
    @0
    wcel
    #
    w3a
    #
    cA
    cB
    c.sm
    wbr
    #
    cB
    cC
    c.sm
    wbr
    #
    wa
    #
    cA
    cC
    c.sm
    wbr
    #
    @7
    @1
    @2
    @3
    wa
    #
    wa
    @4
    @5
    @1
    @6
    @9
    @5
    @1
    @2
    cA
    cB
    @0
    @0
    c.sm
    c.sm
    vx
    cv
    #
    @0
    wcel
    vy
    cv
    #
    @0
    wcel
    wa
    @10
    vz
    cv
    #
    vw
    cv
    #
    cop
    wceq
    @11
    vv
    cv
    #
    vu
    cv
    #
    cop
    wceq
    wa
    @12
    @15
    c.pl
    co
    @13
    @14
    c.pl
    co
    wceq
    wa
    vu
    wex
    vv
    wex
    vw
    wex
    vz
    wex
    #
    wa
    vx
    vy
    copab
    @0
    @0
    cxp
    ecopopr.1
    @16
    vx
    vy
    @0
    @0
    opabssxp
    eqsstri
    #
    brel
    simpld
    cB
    cC
    @0
    @0
    c.sm
    @17
    brel
    anim12i
    @1
    @2
    @3
    3anass
    sylibr
    vf
    cv
    #
    vg
    cv
    #
    cop
    #
    vh
    cv
    #
    vt
    cv
    #
    cop
    #
    c.sm
    wbr
    #
    @23
    vs
    cv
    #
    vr
    cv
    #
    cop
    #
    c.sm
    wbr
    #
    wa
    #
    @20
    @27
    c.sm
    wbr
    #
    wi
    cA
    @23
    c.sm
    wbr
    #
    @28
    wa
    #
    cA
    @27
    c.sm
    wbr
    #
    wi
    @5
    cB
    @27
    c.sm
    wbr
    #
    wa
    #
    @33
    wi
    @7
    @8
    wi
    vf
    vg
    vh
    vt
    vs
    vr
    cA
    cB
    cC
    cS
    @0
    cS
    @0
    eqid
    @20
    cA
    wceq
    #
    @29
    @32
    @30
    @33
    @36
    @24
    @31
    @28
    @20
    cA
    @23
    c.sm
    breq1
    anbi1d
    @20
    cA
    @27
    c.sm
    breq1
    imbi12d
    @23
    cB
    wceq
    #
    @32
    @35
    @33
    @37
    @31
    @5
    @28
    @34
    @23
    cB
    cA
    c.sm
    breq2
    @23
    cB
    @27
    c.sm
    breq1
    anbi12d
    imbi1d
    @27
    cC
    wceq
    #
    @35
    @7
    @33
    @8
    @38
    @34
    @6
    @5
    @27
    cC
    cB
    c.sm
    breq2
    anbi2d
    @27
    cC
    cA
    c.sm
    breq2
    imbi12d
    @18
    cS
    wcel
    #
    @19
    cS
    wcel
    #
    wa
    #
    @21
    cS
    wcel
    @22
    cS
    wcel
    wa
    #
    @25
    cS
    wcel
    #
    @26
    cS
    wcel
    #
    wa
    #
    w3a
    #
    @29
    @18
    @26
    c.pl
    co
    #
    @19
    @25
    c.pl
    co
    #
    wceq
    #
    @30
    @46
    @29
    @21
    @22
    c.pl
    co
    #
    @47
    c.pl
    co
    #
    @50
    @48
    c.pl
    co
    #
    wceq
    #
    @49
    @46
    @29
    @18
    @22
    c.pl
    co
    #
    @19
    @21
    c.pl
    co
    #
    wceq
    #
    @21
    @26
    c.pl
    co
    #
    @22
    @25
    c.pl
    co
    #
    wceq
    #
    wa
    #
    @53
    @46
    @24
    @56
    @28
    @59
    @41
    @42
    @24
    @56
    wb
    @45
    vx
    vy
    vz
    vw
    vv
    vu
    @18
    @19
    @21
    @22
    c.pl
    c.sm
    cS
    ecopopr.1
    ecopoveq
    3adant3
    @42
    @45
    @28
    @59
    wb
    @41
    vx
    vy
    vz
    vw
    vv
    vu
    @21
    @22
    @25
    @26
    c.pl
    c.sm
    cS
    ecopopr.1
    ecopoveq
    3adant1
    anbi12d
    @60
    @54
    @57
    c.pl
    co
    @55
    @58
    c.pl
    co
    #
    @51
    @52
    @54
    @55
    @57
    @58
    c.pl
    oveq12
    vx
    vy
    vz
    @21
    @22
    @18
    @26
    c.pl
    vh
    vex
    #
    vt
    vex
    #
    vf
    vex
    ecopopr.com
    ecopopr.ass
    vr
    vex
    caov411
    @19
    @22
    c.pl
    co
    @21
    @25
    c.pl
    co
    c.pl
    co
    @52
    @61
    vx
    vy
    vz
    @19
    @22
    @21
    @25
    c.pl
    vg
    vex
    #
    @63
    @62
    ecopopr.com
    ecopopr.ass
    vs
    vex
    #
    caov411
    vx
    vy
    vz
    @19
    @22
    @21
    @25
    c.pl
    @64
    @63
    @62
    ecopopr.com
    ecopopr.ass
    @65
    caov4
    eqtr3i
    3eqtr4g
    syl6bi
    @39
    @42
    @45
    @53
    @49
    wi
    #
    @40
    @39
    @42
    @44
    @66
    @43
    @42
    @39
    @44
    @66
    @42
    @39
    @44
    @66
    @42
    @50
    cS
    wcel
    @47
    cS
    wcel
    @66
    @39
    @44
    wa
    vx
    vy
    @21
    @22
    cS
    c.pl
    ecopopr.cl
    caovcl
    vx
    vy
    @18
    @26
    cS
    c.pl
    ecopopr.cl
    caovcl
    vx
    vy
    vz
    @50
    @47
    @48
    cS
    c.pl
    @19
    @25
    c.pl
    ovex
    ecopopr.can
    caovcan
    syl2an
    3impb
    3com12
    3adant3l
    3adant1r
    syld
    @41
    @45
    @30
    @49
    wb
    @42
    vx
    vy
    vz
    vw
    vv
    vu
    @18
    @19
    @25
    @26
    c.pl
    c.sm
    cS
    ecopopr.1
    ecopoveq
    3adant2
    sylibrd
    3optocl
    mpcom
end
