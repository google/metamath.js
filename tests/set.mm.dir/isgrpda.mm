include "cgr.mm"
include "wcel.mm"
include "crn.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "w3a.mm"
include "ralrimivvva.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "cbvrexv.mm"
include "sylibr.mm"
include "jca.mm"
include "ralrimiva.mm"
include "eqeq2.mm"
include "rexbidv.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wfo.mm"
include "adantr.mm"
include "simpr.mm"
include "eqcomd.mm"
include "rspceov.mm"
include "syl3anc.mm"
include "foov.mm"
include "sylanbrc.mm"
include "forn.mm"
include "syl.mm"
include "sqxpeqd.mm"
include "feq23d.mm"
include "raleqdv.mm"
include "raleqbidv.mm"
include "rexeqdv.mm"
include "anbi2d.mm"
include "rexeqbidv.mm"
include "3anbi123d.mm"
include "mpbir3and.mm"
include "cvv.mm"
include "wb.mm"
include "xpexg.mm"
include "fex.mm"
include "eqid.mm"
include "isgrpo.mm"
include "mpbird.mm"

theorem isgrpda
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cU: class U
  let vn: setvar n
  let cG: class G
  let cX: class X
  let vu: setvar u
  assume isgrpda.1: |- ( ph -> X e. _V )
  assume isgrpda.2: |- ( ph -> G : ( X X. X ) --> X )
  assume isgrpda.3: |- ( ( ph /\ ( x e. X /\ y e. X /\ z e. X ) ) -> ( ( x G y ) G z ) = ( x G ( y G z ) ) )
  assume isgrpda.4: |- ( ph -> U e. X )
  assume isgrpda.5: |- ( ( ph /\ x e. X ) -> ( U G x ) = x )
  assume isgrpda.6: |- ( ( ph /\ x e. X ) -> E. n e. X ( n G x ) = U )

  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint X n
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint U n
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint ph u
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint n u
  disjoint X u
  disjoint U u
  assert |- ( ph -> G e. GrpOp )

  proof
    wph
    cG
    cgr
    wcel
    #
    cG
    crn
    #
    @1
    cxp
    #
    @1
    cG
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    co
    vz
    cv
    #
    cG
    co
    @4
    @5
    @6
    cG
    co
    #
    cG
    co
    wceq
    #
    vz
    @1
    wral
    #
    vy
    @1
    wral
    #
    vx
    @1
    wral
    #
    vu
    cv
    #
    @4
    cG
    co
    #
    @4
    wceq
    #
    @5
    @4
    cG
    co
    #
    @12
    wceq
    #
    vy
    @1
    wrex
    #
    wa
    #
    vx
    @1
    wral
    #
    vu
    @1
    wrex
    #
    w3a
    #
    wph
    @21
    cX
    cX
    cxp
    #
    cX
    cG
    wf
    #
    @8
    vz
    cX
    wral
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    #
    @14
    @16
    vy
    cX
    wrex
    #
    wa
    #
    vx
    cX
    wral
    #
    vu
    cX
    wrex
    #
    isgrpda.2
    wph
    @8
    vx
    vy
    vz
    cX
    cX
    cX
    isgrpda.3
    ralrimivvva
    wph
    cU
    cX
    wcel
    #
    cU
    @4
    cG
    co
    #
    @4
    wceq
    #
    @15
    cU
    wceq
    #
    vy
    cX
    wrex
    #
    wa
    #
    vx
    cX
    wral
    #
    @30
    isgrpda.4
    wph
    @36
    vx
    cX
    wph
    @4
    cX
    wcel
    #
    wa
    #
    @33
    @35
    isgrpda.5
    @39
    vn
    cv
    #
    @4
    cG
    co
    #
    cU
    wceq
    #
    vn
    cX
    wrex
    @35
    isgrpda.6
    @34
    @42
    vy
    vn
    cX
    @5
    @40
    wceq
    @15
    @41
    cU
    @5
    @40
    @4
    cG
    oveq1
    eqeq1d
    cbvrexv
    sylibr
    jca
    ralrimiva
    @29
    @37
    vu
    cU
    cX
    @12
    cU
    wceq
    #
    @28
    @36
    vx
    cX
    @43
    @14
    @33
    @27
    @35
    @43
    @13
    @32
    @4
    @12
    cU
    @4
    cG
    oveq1
    eqeq1d
    @43
    @16
    @34
    vy
    cX
    @12
    cU
    @15
    eqeq2
    rexbidv
    anbi12d
    ralbidv
    rspcev
    syl2anc
    wph
    @3
    @23
    @11
    @26
    @20
    @30
    wph
    @2
    @1
    @22
    cX
    cG
    wph
    @1
    cX
    wph
    @22
    cX
    cG
    wfo
    #
    @1
    cX
    wceq
    wph
    @23
    @4
    @7
    wceq
    vz
    cX
    wrex
    vy
    cX
    wrex
    #
    vx
    cX
    wral
    @44
    isgrpda.2
    wph
    @45
    vx
    cX
    @39
    @31
    @38
    @4
    @32
    wceq
    @45
    wph
    @31
    @38
    isgrpda.4
    adantr
    wph
    @38
    simpr
    @39
    @32
    @4
    isgrpda.5
    eqcomd
    vy
    vz
    cX
    cX
    cU
    @4
    @4
    cG
    rspceov
    syl3anc
    ralrimiva
    vy
    vz
    vx
    cX
    cX
    cX
    cG
    foov
    sylanbrc
    @22
    cX
    cG
    forn
    syl
    #
    sqxpeqd
    @46
    feq23d
    wph
    @10
    @25
    vx
    @1
    cX
    @46
    wph
    @9
    @24
    vy
    @1
    cX
    @46
    wph
    @8
    vz
    @1
    cX
    @46
    raleqdv
    raleqbidv
    raleqbidv
    wph
    @19
    @29
    vu
    @1
    cX
    @46
    wph
    @18
    @28
    vx
    @1
    cX
    @46
    wph
    @17
    @27
    @14
    wph
    @16
    vy
    @1
    cX
    @46
    rexeqdv
    anbi2d
    raleqbidv
    rexeqbidv
    3anbi123d
    mpbir3and
    wph
    cG
    cvv
    wcel
    #
    @0
    @21
    wb
    wph
    @23
    @22
    cvv
    wcel
    #
    @47
    isgrpda.2
    wph
    cX
    cvv
    wcel
    #
    @49
    @48
    isgrpda.1
    isgrpda.1
    cX
    cX
    cvv
    cvv
    xpexg
    syl2anc
    @22
    cX
    cvv
    cG
    fex
    syl2anc
    vx
    vy
    vz
    vu
    cvv
    cG
    @1
    @1
    eqid
    isgrpo
    syl
    mpbird
end
