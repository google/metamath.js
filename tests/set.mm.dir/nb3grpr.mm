include "cpr.mm"
include "wcel.mm"
include "w3a.mm"
include "cnbgr.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "ctp.mm"
include "wral.mm"
include "wa.mm"
include "wb.mm"
include "id.mm"
include "prcom.mm"
include "eleq1i.mm"
include "3anbi123i.mm"
include "3anrot.mm"
include "bitr4i.mm"
include "a1i.mm"
include "biadan2.mm"
include "an6.mm"
include "bitri.mm"
include "nb3grprlem1.mm"
include "tprot.mm"
include "syl6eq.mm"
include "sylib.mm"
include "syl6eqr.mm"
include "sylibr.mm"
include "3anbi123d.mm"
include "nb3grprlem2.mm"
include "wne.mm"
include "necom.mm"
include "biid.mm"
include "3bitr2d.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "2rexbidv.mm"
include "raltpg.mm"
include "syl.mm"
include "raleq.mm"
include "bicomd.mm"

theorem nb3grpr
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vv: setvar v
  let vw: setvar w
  assume nb3grpr.v: |- V = ( Vtx ` G )
  assume nb3grpr.e: |- E = ( Edg ` G )
  assume nb3grpr.g: |- ( ph -> G e. USGraph )
  assume nb3grpr.t: |- ( ph -> V = { A , B , C } )
  assume nb3grpr.s: |- ( ph -> ( A e. X /\ B e. Y /\ C e. Z ) )
  assume nb3grpr.n: |- ( ph -> ( A =/= B /\ A =/= C /\ B =/= C ) )

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint E y
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint ph y
  disjoint A v
  disjoint B v
  disjoint C v
  disjoint E v
  disjoint G v
  disjoint V v
  disjoint ph v
  disjoint A w
  disjoint v w
  disjoint B w
  disjoint C w
  disjoint G w
  disjoint V w
  assert |- ( ph -> ( ( { A , B } e. E /\ { B , C } e. E /\ { C , A } e. E ) <-> A. x e. V E. y e. V E. z e. ( V \ { y } ) ( G NeighbVtx x ) = { y , z } ) )

  proof
    wph
    cA
    cB
    cpr
    #
    cE
    wcel
    #
    cB
    cC
    cpr
    #
    cE
    wcel
    #
    cC
    cA
    cpr
    #
    cE
    wcel
    #
    w3a
    #
    cG
    cA
    cnbgr
    co
    #
    vy
    cv
    #
    vz
    cv
    cpr
    #
    wceq
    #
    vz
    cV
    @8
    csn
    cdif
    #
    wrex
    vy
    cV
    wrex
    #
    cG
    cB
    cnbgr
    co
    #
    @9
    wceq
    #
    vz
    @11
    wrex
    vy
    cV
    wrex
    #
    cG
    cC
    cnbgr
    co
    #
    @9
    wceq
    #
    vz
    @11
    wrex
    vy
    cV
    wrex
    #
    w3a
    #
    cG
    vx
    cv
    #
    cnbgr
    co
    #
    @9
    wceq
    #
    vz
    @11
    wrex
    vy
    cV
    wrex
    #
    vx
    cA
    cB
    cC
    ctp
    #
    wral
    #
    @23
    vx
    cV
    wral
    #
    wph
    @6
    @1
    cA
    cC
    cpr
    #
    cE
    wcel
    #
    wa
    #
    @3
    cB
    cA
    cpr
    #
    cE
    wcel
    #
    wa
    #
    @5
    cC
    cB
    cpr
    #
    cE
    wcel
    #
    wa
    #
    w3a
    #
    @7
    @2
    wceq
    #
    @13
    @4
    wceq
    #
    @16
    @0
    wceq
    #
    w3a
    @19
    @6
    @36
    wb
    wph
    @6
    @6
    @28
    @31
    @34
    w3a
    #
    wa
    @36
    @6
    @6
    @40
    @6
    id
    @6
    @40
    wb
    @6
    @6
    @31
    @34
    @28
    w3a
    @40
    @1
    @31
    @3
    @34
    @5
    @28
    @0
    @30
    cE
    cA
    cB
    prcom
    eleq1i
    @2
    @33
    cE
    cB
    cC
    prcom
    eleq1i
    @4
    @27
    cE
    cC
    cA
    prcom
    eleq1i
    3anbi123i
    @28
    @31
    @34
    3anrot
    bitr4i
    a1i
    biadan2
    @1
    @3
    @5
    @28
    @31
    @34
    an6
    bitri
    a1i
    wph
    @37
    @29
    @38
    @32
    @39
    @35
    wph
    cA
    cB
    cC
    cE
    cG
    cV
    cX
    cY
    cZ
    nb3grpr.v
    nb3grpr.e
    nb3grpr.g
    nb3grpr.t
    nb3grpr.s
    nb3grprlem1
    wph
    cB
    cC
    cA
    cE
    cG
    cV
    cY
    cZ
    cX
    nb3grpr.v
    nb3grpr.e
    nb3grpr.g
    wph
    cV
    @24
    cB
    cC
    cA
    ctp
    nb3grpr.t
    cA
    cB
    cC
    tprot
    syl6eq
    #
    wph
    cA
    cX
    wcel
    #
    cB
    cY
    wcel
    #
    cC
    cZ
    wcel
    #
    w3a
    #
    @43
    @44
    @42
    w3a
    nb3grpr.s
    @42
    @43
    @44
    3anrot
    sylib
    #
    nb3grprlem1
    wph
    cC
    cA
    cB
    cE
    cG
    cV
    cZ
    cX
    cY
    nb3grpr.v
    nb3grpr.e
    nb3grpr.g
    wph
    cV
    @24
    cC
    cA
    cB
    ctp
    nb3grpr.t
    cC
    cA
    cB
    tprot
    syl6eqr
    #
    wph
    @45
    @44
    @42
    @43
    w3a
    nb3grpr.s
    @44
    @42
    @43
    3anrot
    sylibr
    #
    nb3grprlem1
    3anbi123d
    wph
    @37
    @12
    @38
    @15
    @39
    @18
    wph
    vz
    vy
    cA
    cB
    cC
    cE
    cG
    cV
    cX
    cY
    cZ
    nb3grpr.v
    nb3grpr.e
    nb3grpr.g
    nb3grpr.t
    nb3grpr.s
    nb3grpr.n
    nb3grprlem2
    wph
    vz
    vy
    cB
    cC
    cA
    cE
    cG
    cV
    cY
    cZ
    cX
    nb3grpr.v
    nb3grpr.e
    nb3grpr.g
    @41
    @46
    wph
    cA
    cB
    wne
    #
    cA
    cC
    wne
    #
    cB
    cC
    wne
    #
    w3a
    #
    @51
    cB
    cA
    wne
    #
    cC
    cA
    wne
    #
    w3a
    #
    nb3grpr.n
    @52
    @53
    @54
    @51
    w3a
    @55
    @49
    @53
    @50
    @54
    @51
    @51
    cA
    cB
    necom
    cA
    cC
    necom
    #
    @51
    biid
    3anbi123i
    @51
    @53
    @54
    3anrot
    bitr4i
    sylib
    nb3grprlem2
    wph
    vz
    vy
    cC
    cA
    cB
    cE
    cG
    cV
    cZ
    cX
    cY
    nb3grpr.v
    nb3grpr.e
    nb3grpr.g
    @47
    @48
    wph
    @52
    @54
    cC
    cB
    wne
    #
    @49
    w3a
    #
    nb3grpr.n
    @52
    @50
    @51
    @49
    w3a
    @58
    @49
    @50
    @51
    3anrot
    @50
    @54
    @51
    @57
    @49
    @49
    @56
    cB
    cC
    necom
    @49
    biid
    3anbi123i
    bitri
    sylib
    nb3grprlem2
    3anbi123d
    3bitr2d
    wph
    @45
    @25
    @19
    wb
    nb3grpr.s
    @23
    @12
    @15
    @18
    vx
    cA
    cB
    cC
    cX
    cY
    cZ
    @20
    cA
    wceq
    #
    @22
    @10
    vy
    vz
    cV
    @11
    @59
    @21
    @7
    @9
    @20
    cA
    cG
    cnbgr
    oveq2
    eqeq1d
    2rexbidv
    @20
    cB
    wceq
    #
    @22
    @14
    vy
    vz
    cV
    @11
    @60
    @21
    @13
    @9
    @20
    cB
    cG
    cnbgr
    oveq2
    eqeq1d
    2rexbidv
    @20
    cC
    wceq
    #
    @22
    @17
    vy
    vz
    cV
    @11
    @61
    @21
    @16
    @9
    @20
    cC
    cG
    cnbgr
    oveq2
    eqeq1d
    2rexbidv
    raltpg
    syl
    wph
    cV
    @24
    wceq
    #
    @25
    @26
    wb
    nb3grpr.t
    @62
    @26
    @25
    @23
    vx
    cV
    @24
    raleq
    bicomd
    syl
    3bitr2d
end
