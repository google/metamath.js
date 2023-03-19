include "cn0.mm"
include "cxp.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "c2nd.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "cres.mm"
include "xp2nd.mm"
include "syl5eqel.mm"
include "eluznn0.mm"
include "sylan.mm"
include "nn0uz.mm"
include "0zd.mm"
include "id.mm"
include "wf.mm"
include "eucalgf.mm"
include "a1i.mm"
include "algrf.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "fvres.mm"
include "syl.mm"
include "simpl.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "f2ndres.mm"
include "cv.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "eucalglt.mm"
include "ffvelrni.mm"
include "neeq1d.mm"
include "breq12d.mm"
include "3imtr4d.mm"
include "eqid.mm"
include "algcvga.mm"
include "sylc.mm"
include "eqtr3d.mm"
include "ex.mm"

theorem eucalgcvga
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cE: class E
  let cK: class K
  let cN: class N
  let cM: class M
  let cX: class X
  let vz: setvar z
  assume eucalgval.1: |- E = ( x e. NN0 , y e. NN0 |-> if ( y = 0 , <. x , y >. , <. y , ( x mod y ) >. ) )
  assume eucalg.2: |- R = seq 0 ( ( E o. 1st ) , ( NN0 X. { A } ) )
  assume eucalgcvga.3: |- N = ( 2nd ` A )

  disjoint x y
  disjoint N x
  disjoint N y
  disjoint A x
  disjoint A y
  disjoint R x
  disjoint M x
  disjoint M y
  disjoint X x
  disjoint X y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint R z
  disjoint E z
  assert |- ( A e. ( NN0 X. NN0 ) -> ( K e. ( ZZ>= ` N ) -> ( 2nd ` ( R ` K ) ) = 0 ) )

  proof
    cA
    cn0
    cn0
    cxp
    #
    wcel
    #
    cK
    cN
    cuz
    cfv
    #
    wcel
    #
    cK
    cR
    cfv
    #
    c2nd
    cfv
    #
    cc0
    wceq
    @1
    @3
    wa
    #
    @4
    c2nd
    @0
    cres
    #
    cfv
    #
    @5
    cc0
    @6
    @4
    @0
    wcel
    #
    @8
    @5
    wceq
    @1
    @3
    cK
    cn0
    wcel
    #
    @9
    @1
    cN
    cn0
    wcel
    @3
    @10
    @1
    cN
    cA
    c2nd
    cfv
    #
    cn0
    eucalgcvga.3
    cA
    cn0
    cn0
    xp2nd
    syl5eqel
    cK
    cN
    eluznn0
    sylan
    @1
    cn0
    @0
    cK
    cR
    @1
    cA
    cR
    @0
    cE
    cc0
    cn0
    nn0uz
    eucalg.2
    @1
    0zd
    @1
    id
    @0
    @0
    cE
    wf
    @1
    vx
    vy
    cE
    eucalgval.1
    eucalgf
    #
    a1i
    algrf
    ffvelrnda
    syldan
    @4
    @0
    c2nd
    fvres
    syl
    @6
    @1
    cK
    cA
    @7
    cfv
    #
    cuz
    cfv
    #
    wcel
    #
    @8
    cc0
    wceq
    @1
    @3
    simpl
    @1
    @15
    @3
    @1
    @14
    @2
    cK
    @1
    @13
    cN
    cuz
    @1
    @13
    @11
    cN
    cA
    @0
    c2nd
    fvres
    eucalgcvga.3
    syl6eqr
    fveq2d
    eleq2d
    biimpar
    vz
    cA
    @7
    cR
    @0
    cE
    cK
    @13
    @12
    eucalg.2
    cn0
    cn0
    f2ndres
    vz
    cv
    #
    @0
    wcel
    #
    @16
    cE
    cfv
    #
    c2nd
    cfv
    #
    cc0
    wne
    @19
    @16
    c2nd
    cfv
    #
    clt
    wbr
    @18
    @7
    cfv
    #
    cc0
    wne
    @21
    @16
    @7
    cfv
    #
    clt
    wbr
    vx
    vy
    cE
    @16
    eucalgval.1
    eucalglt
    @17
    @21
    @19
    cc0
    @17
    @18
    @0
    wcel
    @21
    @19
    wceq
    @0
    @0
    @16
    cE
    @12
    ffvelrni
    @18
    @0
    c2nd
    fvres
    syl
    #
    neeq1d
    @17
    @21
    @19
    @22
    @20
    clt
    @23
    @16
    @0
    c2nd
    fvres
    breq12d
    3imtr4d
    @13
    eqid
    algcvga
    sylc
    eqtr3d
    ex
end
