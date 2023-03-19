include "crh.mm"
include "co.mm"
include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cghm.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmhm.mm"
include "ringpropd.mm"
include "anbi12d.mm"
include "ghmpropd.mm"
include "eleq2d.mm"
include "cbs.mm"
include "eqid.mm"
include "mgpbas.mm"
include "syl6eq.mm"
include "cmulr.mm"
include "cplusg.mm"
include "mgpplusg.mm"
include "oveqi.mm"
include "3eqtr3g.mm"
include "mhmpropd.mm"
include "isrhm.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem rhmpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let vf: setvar f
  assume rhmpropd.a: |- ( ph -> B = ( Base ` J ) )
  assume rhmpropd.b: |- ( ph -> C = ( Base ` K ) )
  assume rhmpropd.c: |- ( ph -> B = ( Base ` L ) )
  assume rhmpropd.d: |- ( ph -> C = ( Base ` M ) )
  assume rhmpropd.e: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` J ) y ) = ( x ( +g ` L ) y ) )
  assume rhmpropd.f: |- ( ( ph /\ ( x e. C /\ y e. C ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` M ) y ) )
  assume rhmpropd.g: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( .r ` J ) y ) = ( x ( .r ` L ) y ) )
  assume rhmpropd.h: |- ( ( ph /\ ( x e. C /\ y e. C ) ) -> ( x ( .r ` K ) y ) = ( x ( .r ` M ) y ) )

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint M x
  disjoint M y
  disjoint ph x
  disjoint ph y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint f x
  disjoint f y
  disjoint J f
  disjoint K f
  disjoint L f
  disjoint M f
  disjoint f ph
  assert |- ( ph -> ( J RingHom K ) = ( L RingHom M ) )

  proof
    wph
    vf
    cJ
    cK
    crh
    co
    #
    cL
    cM
    crh
    co
    #
    wph
    cJ
    crg
    wcel
    #
    cK
    crg
    wcel
    #
    wa
    #
    vf
    cv
    #
    cJ
    cK
    cghm
    co
    #
    wcel
    #
    @5
    cJ
    cmgp
    cfv
    #
    cK
    cmgp
    cfv
    #
    cmhm
    co
    #
    wcel
    #
    wa
    #
    wa
    cL
    crg
    wcel
    #
    cM
    crg
    wcel
    #
    wa
    #
    @5
    cL
    cM
    cghm
    co
    #
    wcel
    #
    @5
    cL
    cmgp
    cfv
    #
    cM
    cmgp
    cfv
    #
    cmhm
    co
    #
    wcel
    #
    wa
    #
    wa
    @5
    @0
    wcel
    @5
    @1
    wcel
    wph
    @4
    @15
    @12
    @22
    wph
    @2
    @13
    @3
    @14
    wph
    vx
    vy
    cB
    cJ
    cL
    rhmpropd.a
    rhmpropd.c
    rhmpropd.e
    rhmpropd.g
    ringpropd
    wph
    vx
    vy
    cC
    cK
    cM
    rhmpropd.b
    rhmpropd.d
    rhmpropd.f
    rhmpropd.h
    ringpropd
    anbi12d
    wph
    @7
    @17
    @11
    @21
    wph
    @6
    @16
    @5
    wph
    vx
    vy
    cB
    cC
    cJ
    cK
    cL
    cM
    rhmpropd.a
    rhmpropd.b
    rhmpropd.c
    rhmpropd.d
    rhmpropd.e
    rhmpropd.f
    ghmpropd
    eleq2d
    wph
    @10
    @20
    @5
    wph
    vx
    vy
    cB
    cC
    @8
    @9
    @18
    @19
    wph
    cB
    cJ
    cbs
    cfv
    #
    @8
    cbs
    cfv
    rhmpropd.a
    @23
    cJ
    @8
    @8
    eqid
    #
    @23
    eqid
    mgpbas
    syl6eq
    wph
    cC
    cK
    cbs
    cfv
    #
    @9
    cbs
    cfv
    rhmpropd.b
    @25
    cK
    @9
    @9
    eqid
    #
    @25
    eqid
    mgpbas
    syl6eq
    wph
    cB
    cL
    cbs
    cfv
    #
    @18
    cbs
    cfv
    rhmpropd.c
    @27
    cL
    @18
    @18
    eqid
    #
    @27
    eqid
    mgpbas
    syl6eq
    wph
    cC
    cM
    cbs
    cfv
    #
    @19
    cbs
    cfv
    rhmpropd.d
    @29
    cM
    @19
    @19
    eqid
    #
    @29
    eqid
    mgpbas
    syl6eq
    wph
    vx
    cv
    #
    cB
    wcel
    vy
    cv
    #
    cB
    wcel
    wa
    wa
    @31
    @32
    cJ
    cmulr
    cfv
    #
    co
    @31
    @32
    cL
    cmulr
    cfv
    #
    co
    @31
    @32
    @8
    cplusg
    cfv
    #
    co
    @31
    @32
    @18
    cplusg
    cfv
    #
    co
    rhmpropd.g
    @33
    @35
    @31
    @32
    cJ
    @33
    @8
    @24
    @33
    eqid
    mgpplusg
    oveqi
    @34
    @36
    @31
    @32
    cL
    @34
    @18
    @28
    @34
    eqid
    mgpplusg
    oveqi
    3eqtr3g
    wph
    @31
    cC
    wcel
    @32
    cC
    wcel
    wa
    wa
    @31
    @32
    cK
    cmulr
    cfv
    #
    co
    @31
    @32
    cM
    cmulr
    cfv
    #
    co
    @31
    @32
    @9
    cplusg
    cfv
    #
    co
    @31
    @32
    @19
    cplusg
    cfv
    #
    co
    rhmpropd.h
    @37
    @39
    @31
    @32
    cK
    @37
    @9
    @26
    @37
    eqid
    mgpplusg
    oveqi
    @38
    @40
    @31
    @32
    cM
    @38
    @19
    @30
    @38
    eqid
    mgpplusg
    oveqi
    3eqtr3g
    mhmpropd
    eleq2d
    anbi12d
    anbi12d
    cJ
    cK
    @5
    @8
    @9
    @24
    @26
    isrhm
    cL
    cM
    @5
    @18
    @19
    @28
    @30
    isrhm
    3bitr4g
    eqrdv
end
