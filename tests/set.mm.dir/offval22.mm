include "cof.mm"
include "co.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "csb.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "cvv.mm"
include "wcel.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "wa.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "jca.mm"
include "w3a.mm"
include "wi.mm"
include "fvex.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "3anbi3d.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "3anbi2d.mm"
include "elex.mm"
include "syl.mm"
include "vtocl2gf.mm"
include "mp2an.mm"
include "3expb.mm"
include "sylan2.mm"
include "mpt2mpts.mm"
include "syl6eq.mm"
include "offval2.mm"
include "csbov12g.mm"
include "csbeq2dv.mm"
include "ax-mp.mm"
include "eqtr2i.mm"
include "mpteq2i.mm"
include "eqtr4i.mm"

theorem offval22
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vz: setvar z
  assume offval22.a: |- ( ph -> A e. V )
  assume offval22.b: |- ( ph -> B e. W )
  assume offval22.c: |- ( ( ph /\ x e. A /\ y e. B ) -> C e. X )
  assume offval22.d: |- ( ( ph /\ x e. A /\ y e. B ) -> D e. Y )
  assume offval22.f: |- ( ph -> F = ( x e. A , y e. B |-> C ) )
  assume offval22.g: |- ( ph -> G = ( x e. A , y e. B |-> D ) )

  disjoint ph x
  disjoint ph y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  disjoint ph z
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint R z
  disjoint C z
  disjoint D z
  assert |- ( ph -> ( F oF R G ) = ( x e. A , y e. B |-> ( C R D ) ) )

  proof
    wph
    cF
    cG
    cR
    cof
    co
    vz
    cA
    cB
    cxp
    #
    vx
    vz
    cv
    #
    c1st
    cfv
    #
    vy
    @1
    c2nd
    cfv
    #
    cC
    csb
    #
    csb
    #
    vx
    @2
    vy
    @3
    cD
    csb
    #
    csb
    #
    cR
    co
    #
    cmpt
    #
    vx
    vy
    cA
    cB
    cC
    cD
    cR
    co
    #
    cmpt2
    #
    wph
    vz
    @0
    @5
    @7
    cR
    cF
    cG
    cvv
    cvv
    cvv
    wph
    cA
    cV
    wcel
    cB
    cW
    wcel
    @0
    cvv
    wcel
    offval22.a
    offval22.b
    cA
    cB
    cV
    cW
    xpexg
    syl2anc
    @1
    @0
    wcel
    #
    wph
    @2
    cA
    wcel
    #
    @3
    cB
    wcel
    #
    wa
    #
    @5
    cvv
    wcel
    #
    @12
    @13
    @14
    @1
    cA
    cB
    xp1st
    @1
    cA
    cB
    xp2nd
    jca
    #
    wph
    @13
    @14
    @16
    @3
    cvv
    wcel
    #
    @2
    cvv
    wcel
    #
    wph
    @13
    @14
    w3a
    #
    @16
    wi
    #
    @1
    c2nd
    fvex
    #
    @1
    c1st
    fvex
    #
    wph
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    w3a
    #
    cC
    cvv
    wcel
    #
    wi
    wph
    @25
    @14
    w3a
    #
    @4
    cvv
    wcel
    #
    wi
    @21
    vy
    vx
    @3
    @2
    cvv
    cvv
    vy
    @3
    nfcv
    #
    vx
    @3
    nfcv
    #
    vx
    @2
    nfcv
    #
    @30
    @31
    vy
    @30
    vy
    nfv
    #
    vy
    @4
    cvv
    vy
    @3
    cC
    nfcsb1v
    nfel1
    nfim
    @20
    @16
    vx
    @20
    vx
    nfv
    #
    vx
    @5
    cvv
    vx
    @2
    @4
    nfcsb1v
    nfel1
    nfim
    @26
    @3
    wceq
    #
    @28
    @30
    @29
    @31
    @37
    @27
    @14
    wph
    @25
    @26
    @3
    cB
    eleq1
    3anbi3d
    #
    @37
    cC
    @4
    cvv
    vy
    @3
    cC
    csbeq1a
    eleq1d
    imbi12d
    @24
    @2
    wceq
    #
    @30
    @20
    @31
    @16
    @39
    @25
    @13
    wph
    @14
    @24
    @2
    cA
    eleq1
    3anbi2d
    #
    @39
    @4
    @5
    cvv
    vx
    @2
    @4
    csbeq1a
    eleq1d
    imbi12d
    @28
    cC
    cX
    wcel
    @29
    offval22.c
    cC
    cX
    elex
    syl
    vtocl2gf
    mp2an
    3expb
    sylan2
    @12
    wph
    @15
    @7
    cvv
    wcel
    #
    @17
    wph
    @13
    @14
    @41
    @18
    @19
    @20
    @41
    wi
    #
    @22
    @23
    @28
    cD
    cvv
    wcel
    #
    wi
    @30
    @6
    cvv
    wcel
    #
    wi
    @42
    vy
    vx
    @3
    @2
    cvv
    cvv
    @32
    @33
    @34
    @30
    @44
    vy
    @35
    vy
    @6
    cvv
    vy
    @3
    cD
    nfcsb1v
    nfel1
    nfim
    @20
    @41
    vx
    @36
    vx
    @7
    cvv
    vx
    @2
    @6
    nfcsb1v
    nfel1
    nfim
    @37
    @28
    @30
    @43
    @44
    @38
    @37
    cD
    @6
    cvv
    vy
    @3
    cD
    csbeq1a
    eleq1d
    imbi12d
    @39
    @30
    @20
    @44
    @41
    @40
    @39
    @6
    @7
    cvv
    vx
    @2
    @6
    csbeq1a
    eleq1d
    imbi12d
    @28
    cD
    cY
    wcel
    @43
    offval22.d
    cD
    cY
    elex
    syl
    vtocl2gf
    mp2an
    3expb
    sylan2
    wph
    cF
    vx
    vy
    cA
    cB
    cC
    cmpt2
    vz
    @0
    @5
    cmpt
    offval22.f
    vx
    vy
    vz
    cA
    cB
    cC
    mpt2mpts
    syl6eq
    wph
    cG
    vx
    vy
    cA
    cB
    cD
    cmpt2
    vz
    @0
    @7
    cmpt
    offval22.g
    vx
    vy
    vz
    cA
    cB
    cD
    mpt2mpts
    syl6eq
    offval2
    @9
    vz
    @0
    vx
    @2
    vy
    @3
    @10
    csb
    #
    csb
    #
    cmpt
    @11
    vz
    @0
    @8
    @46
    @46
    vx
    @2
    @4
    @6
    cR
    co
    #
    csb
    #
    @8
    @18
    @46
    @48
    wceq
    @22
    @18
    vx
    @2
    @45
    @47
    vy
    @3
    cC
    cD
    cR
    cvv
    csbov12g
    csbeq2dv
    ax-mp
    @19
    @48
    @8
    wceq
    @23
    vx
    @2
    @4
    @6
    cR
    cvv
    csbov12g
    ax-mp
    eqtr2i
    mpteq2i
    vx
    vy
    vz
    cA
    cB
    @10
    mpt2mpts
    eqtr4i
    syl6eq
end
