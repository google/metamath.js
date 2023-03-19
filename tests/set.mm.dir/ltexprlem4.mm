include "cnp.mm"
include "wcel.mm"
include "cv.mm"
include "wn.mm"
include "cplq.mm"
include "co.mm"
include "wa.mm"
include "wex.mm"
include "cltq.mm"
include "wbr.mm"
include "wceq.mm"
include "wrex.mm"
include "prnmax.mm"
include "df-rex.mm"
include "sylib.mm"
include "cnq.mm"
include "ltrelnq.mm"
include "brel.mm"
include "simpld.mm"
include "cxp.mm"
include "addnqf.mm"
include "fdmi.mm"
include "0nnq.mm"
include "ndmovrcl.mm"
include "syl.mm"
include "ltaddnq.mm"
include "ltsonq.mm"
include "sotri.mm"
include "sylan.mm"
include "mpancom.mm"
include "simprd.mm"
include "ltexnq.mm"
include "biimpd.mm"
include "mpcom.mm"
include "eqcom.mm"
include "exbii.mm"
include "sylibr.mm"
include "ancri.mm"
include "anim2i.mm"
include "an12.mm"
include "19.41v.mm"
include "eximi.mm"
include "excom.mm"
include "ovex.mm"
include "eleq1.mm"
include "breq2.mm"
include "anbi12d.mm"
include "ceqsexv.mm"
include "ltanq.mm"
include "ndmovordi.mm"
include "sylbi.mm"
include "3syl.mm"
include "an12s.mm"
include "19.42v.mm"
include "ex.mm"
include "eximdv.mm"
include "abeq2i.mm"
include "vex.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "elab2.mm"
include "anbi1i.mm"
include "anass.mm"
include "3bitr2i.mm"
include "bitr4i.mm"
include "3imtr4g.mm"

theorem ltexprlem4
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vv: setvar v
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vu: setvar u
  assume ltexprlem.1: |- C = { x | E. y ( -. y e. A /\ ( y +Q x ) e. B ) }

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C z
  disjoint w x
  disjoint v x
  disjoint f x
  disjoint g x
  disjoint h x
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
  disjoint A w
  disjoint f v
  disjoint g v
  disjoint h v
  disjoint A v
  disjoint f g
  disjoint f h
  disjoint A f
  disjoint g h
  disjoint A g
  disjoint A h
  disjoint B w
  disjoint B v
  disjoint C w
  disjoint C v
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint u w
  disjoint u v
  disjoint f u
  disjoint g u
  disjoint h u
  assert |- ( B e. P. -> ( x e. C -> E. z ( z e. C /\ x <Q z ) ) )

  proof
    cB
    cnp
    wcel
    #
    vy
    cv
    #
    cA
    wcel
    wn
    #
    @1
    vx
    cv
    #
    cplq
    co
    #
    cB
    wcel
    #
    wa
    #
    vy
    wex
    #
    @2
    @1
    vz
    cv
    #
    cplq
    co
    #
    cB
    wcel
    #
    @3
    @8
    cltq
    wbr
    #
    wa
    #
    wa
    #
    vz
    wex
    #
    vy
    wex
    #
    @3
    cC
    wcel
    @8
    cC
    wcel
    #
    @11
    wa
    #
    vz
    wex
    #
    @0
    @6
    @14
    vy
    @0
    @6
    @14
    @0
    @6
    wa
    @2
    @12
    vz
    wex
    #
    wa
    #
    @14
    @2
    @0
    @5
    @20
    @0
    @5
    wa
    #
    @19
    @2
    @21
    vw
    cv
    #
    cB
    wcel
    #
    @4
    @22
    cltq
    wbr
    #
    wa
    #
    vw
    wex
    #
    @22
    @9
    wceq
    #
    @25
    wa
    #
    vw
    wex
    #
    vz
    wex
    #
    @19
    @21
    @24
    vw
    cB
    wrex
    @26
    vw
    cB
    @4
    prnmax
    @24
    vw
    cB
    df-rex
    sylib
    @26
    @28
    vz
    wex
    #
    vw
    wex
    @30
    @25
    @31
    vw
    @25
    @27
    vz
    wex
    #
    @25
    wa
    #
    @31
    @25
    @23
    @32
    @24
    wa
    #
    wa
    @33
    @24
    @34
    @23
    @24
    @32
    @24
    @9
    @22
    wceq
    #
    vz
    wex
    #
    @32
    @24
    @1
    @22
    cltq
    wbr
    #
    @36
    @1
    cnq
    wcel
    #
    @3
    cnq
    wcel
    wa
    #
    @24
    @37
    @24
    @4
    cnq
    wcel
    #
    @39
    @24
    @40
    @22
    cnq
    wcel
    #
    @4
    @22
    cnq
    cnq
    cltq
    ltrelnq
    brel
    simpld
    @1
    @3
    cnq
    cplq
    cnq
    cnq
    cxp
    cnq
    cplq
    addnqf
    fdmi
    #
    0nnq
    ndmovrcl
    syl
    @39
    @1
    @4
    cltq
    wbr
    @24
    @37
    @1
    @3
    ltaddnq
    @1
    @4
    @22
    cltq
    cnq
    ltsonq
    ltrelnq
    sotri
    sylan
    mpancom
    @41
    @37
    @36
    @37
    @38
    @41
    @1
    @22
    cnq
    cnq
    cltq
    ltrelnq
    brel
    simprd
    @41
    @37
    @36
    vz
    @1
    @22
    ltexnq
    biimpd
    mpcom
    syl
    @27
    @35
    vz
    @22
    @9
    eqcom
    exbii
    sylibr
    ancri
    anim2i
    @32
    @23
    @24
    an12
    sylibr
    @27
    @25
    vz
    19.41v
    sylibr
    eximi
    @28
    vz
    vw
    excom
    sylibr
    @29
    @12
    vz
    @29
    @10
    @4
    @9
    cltq
    wbr
    #
    wa
    #
    @12
    @25
    @44
    vw
    @9
    @1
    @8
    cplq
    ovex
    @27
    @23
    @10
    @24
    @43
    @22
    @9
    cB
    eleq1
    @22
    @9
    @4
    cltq
    breq2
    anbi12d
    ceqsexv
    @43
    @11
    @10
    @3
    @8
    @1
    cltq
    cnq
    cplq
    @42
    ltrelnq
    0nnq
    @3
    @8
    @1
    ltanq
    ndmovordi
    anim2i
    sylbi
    eximi
    3syl
    anim2i
    an12s
    @2
    @12
    vz
    19.42v
    sylibr
    ex
    eximdv
    @7
    vx
    cC
    ltexprlem.1
    abeq2i
    @18
    @13
    vy
    wex
    #
    vz
    wex
    @15
    @17
    @45
    vz
    @17
    @2
    @10
    wa
    #
    vy
    wex
    #
    @11
    wa
    @46
    @11
    wa
    #
    vy
    wex
    @45
    @16
    @47
    @11
    @7
    @47
    vx
    @8
    cC
    vz
    vex
    @3
    @8
    wceq
    #
    @6
    @46
    vy
    @49
    @5
    @10
    @2
    @49
    @4
    @9
    cB
    @3
    @8
    @1
    cplq
    oveq2
    eleq1d
    anbi2d
    exbidv
    ltexprlem.1
    elab2
    anbi1i
    @46
    @11
    vy
    19.41v
    @48
    @13
    vy
    @2
    @10
    @11
    anass
    exbii
    3bitr2i
    exbii
    @13
    vy
    vz
    excom
    bitr4i
    3imtr4g
end
