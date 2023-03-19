include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "cop.mm"
include "co.mm"
include "isseti.mm"
include "nfv.mm"
include "nfcv.mm"
include "cxp.mm"
include "coprab.mm"
include "nfoprab3.mm"
include "nfcxfr.mm"
include "nfov.mm"
include "nfeq1.mm"
include "eqeq2d.mm"
include "copsex4g.mm"
include "wi.mm"
include "opelxpi.mm"
include "nfoprab1.mm"
include "nfim.mm"
include "nfoprab2.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "4exbidv.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "wmo.mm"
include "moeq.mm"
include "mosubop.mm"
include "anass.mm"
include "2exbii.mm"
include "19.42vv.mm"
include "bitri.mm"
include "mobii.mm"
include "mpbir.mm"
include "a1i.mm"
include "ovidi.mm"
include "vtocl2gaf.mm"
include "syl2an.mm"
include "sylbird.mm"
include "eqeq2.mm"
include "mpbidi.mm"
include "exlimd.mm"
include "mpi.mm"

theorem ov3
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
  let cF: class F
  let cH: class H
  assume ov3.1: |- S e. _V
  assume ov3.2: |- ( ( ( w = A /\ v = B ) /\ ( u = C /\ f = D ) ) -> R = S )
  assume ov3.3: |- F = { <. <. x , y >. , z >. | ( ( x e. ( H X. H ) /\ y e. ( H X. H ) ) /\ E. w E. v E. u E. f ( ( x = <. w , v >. /\ y = <. u , f >. ) /\ z = R ) ) }

  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint u v
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
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B f
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint C f
  disjoint C u
  disjoint C v
  disjoint C w
  disjoint C y
  disjoint C z
  disjoint D f
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D y
  disjoint D z
  disjoint H f
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint S f
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S z
  assert |- ( ( ( A e. H /\ B e. H ) /\ ( C e. H /\ D e. H ) ) -> ( <. A , B >. F <. C , D >. ) = S )

  proof
    cA
    cH
    wcel
    cB
    cH
    wcel
    wa
    #
    cC
    cH
    wcel
    cD
    cH
    wcel
    wa
    #
    wa
    #
    vz
    cv
    #
    cS
    wceq
    #
    vz
    wex
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    cF
    co
    #
    cS
    wceq
    #
    vz
    cS
    ov3.1
    isseti
    @2
    @4
    @8
    vz
    @2
    vz
    nfv
    vz
    @7
    cS
    vz
    @5
    @6
    cF
    vz
    @5
    nfcv
    vz
    cF
    vx
    cv
    #
    cH
    cH
    cxp
    #
    wcel
    vy
    cv
    #
    @10
    wcel
    wa
    #
    @9
    vw
    cv
    #
    vv
    cv
    #
    cop
    #
    wceq
    #
    @11
    vu
    cv
    #
    vf
    cv
    #
    cop
    #
    wceq
    #
    wa
    #
    @3
    cR
    wceq
    #
    wa
    #
    vf
    wex
    vu
    wex
    #
    vv
    wex
    vw
    wex
    #
    wa
    #
    vx
    vy
    vz
    coprab
    #
    ov3.3
    @26
    vx
    vy
    vz
    nfoprab3
    nfcxfr
    vz
    @6
    nfcv
    nfov
    nfeq1
    @4
    @7
    @3
    wceq
    #
    @8
    @2
    @2
    @4
    @5
    @15
    wceq
    #
    @6
    @19
    wceq
    #
    wa
    #
    @22
    wa
    #
    vf
    wex
    vu
    wex
    vv
    wex
    vw
    wex
    #
    @28
    @22
    @4
    vw
    vv
    vu
    vf
    cA
    cB
    cC
    cD
    cH
    cH
    @13
    cA
    wceq
    @14
    cB
    wceq
    wa
    @17
    cC
    wceq
    @18
    cD
    wceq
    wa
    wa
    cR
    cS
    @3
    ov3.2
    eqeq2d
    copsex4g
    @0
    @5
    @10
    wcel
    @6
    @10
    wcel
    @33
    @28
    wi
    #
    @1
    cA
    cB
    cH
    cH
    opelxpi
    cC
    cD
    cH
    cH
    opelxpi
    @25
    @9
    @11
    cF
    co
    #
    @3
    wceq
    #
    wi
    @29
    @20
    wa
    #
    @22
    wa
    #
    vf
    wex
    vu
    wex
    vv
    wex
    vw
    wex
    #
    @5
    @11
    cF
    co
    #
    @3
    wceq
    #
    wi
    @34
    vx
    vy
    @5
    @6
    @10
    @10
    vx
    @5
    nfcv
    #
    vy
    @5
    nfcv
    #
    vy
    @6
    nfcv
    #
    @39
    @41
    vx
    @39
    vx
    nfv
    vx
    @40
    @3
    vx
    @5
    @11
    cF
    @42
    vx
    cF
    @27
    ov3.3
    @26
    vx
    vy
    vz
    nfoprab1
    nfcxfr
    vx
    @11
    nfcv
    nfov
    nfeq1
    nfim
    @33
    @28
    vy
    @33
    vy
    nfv
    vy
    @7
    @3
    vy
    @5
    @6
    cF
    @43
    vy
    cF
    @27
    ov3.3
    @26
    vx
    vy
    vz
    nfoprab2
    nfcxfr
    @44
    nfov
    nfeq1
    nfim
    @9
    @5
    wceq
    #
    @25
    @39
    @36
    @41
    @45
    @23
    @38
    vw
    vv
    vu
    vf
    @45
    @21
    @37
    @22
    @45
    @16
    @29
    @20
    @9
    @5
    @15
    eqeq1
    anbi1d
    anbi1d
    4exbidv
    @45
    @35
    @40
    @3
    @9
    @5
    @11
    cF
    oveq1
    eqeq1d
    imbi12d
    @11
    @6
    wceq
    #
    @39
    @33
    @41
    @28
    @46
    @38
    @32
    vw
    vv
    vu
    vf
    @46
    @37
    @31
    @22
    @46
    @20
    @30
    @29
    @11
    @6
    @19
    eqeq1
    anbi2d
    anbi1d
    4exbidv
    @46
    @40
    @7
    @3
    @11
    @6
    @5
    cF
    oveq2
    eqeq1d
    imbi12d
    @25
    vx
    vy
    vz
    @10
    @10
    cF
    @25
    vz
    wmo
    #
    @12
    @47
    @16
    @20
    @22
    wa
    #
    vf
    wex
    vu
    wex
    #
    wa
    #
    vv
    wex
    vw
    wex
    #
    vz
    wmo
    @49
    vz
    vw
    vv
    @9
    @22
    vz
    vu
    vf
    @11
    vz
    cR
    moeq
    mosubop
    mosubop
    @25
    @51
    vz
    @24
    @50
    vw
    vv
    @24
    @16
    @48
    wa
    #
    vf
    wex
    vu
    wex
    @50
    @23
    @52
    vu
    vf
    @16
    @20
    @22
    anass
    2exbii
    @16
    @48
    vu
    vf
    19.42vv
    bitri
    2exbii
    mobii
    mpbir
    a1i
    ov3.3
    ovidi
    vtocl2gaf
    syl2an
    sylbird
    @3
    cS
    @7
    eqeq2
    mpbidi
    exlimd
    mpi
end
