include "cop.mm"
include "crngo.mm"
include "wcel.mm"
include "cablo.mm"
include "crn.mm"
include "cxp.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "wral.mm"
include "wrex.mm"
include "sqxpeqd.mm"
include "feq23d.mm"
include "mpbid.mm"
include "3jca.mm"
include "ralrimivvva.mm"
include "raleqdv.mm"
include "raleqbidv.mm"
include "jca.mm"
include "ralrimiva.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexeqbidv.mm"
include "jca31.mm"
include "cvv.mm"
include "wb.mm"
include "rnexg.mm"
include "syl.mm"
include "xpexg.mm"
include "fex.mm"
include "eqid.mm"
include "isrngo.mm"
include "mpbird.mm"

theorem isrngod
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cU: class U
  let cG: class G
  let cH: class H
  let cX: class X
  assume isringod.1: |- ( ph -> G e. AbelOp )
  assume isringod.2: |- ( ph -> X = ran G )
  assume isringod.3: |- ( ph -> H : ( X X. X ) --> X )
  assume isringod.4: |- ( ( ph /\ ( x e. X /\ y e. X /\ z e. X ) ) -> ( ( x H y ) H z ) = ( x H ( y H z ) ) )
  assume isringod.5: |- ( ( ph /\ ( x e. X /\ y e. X /\ z e. X ) ) -> ( x H ( y G z ) ) = ( ( x H y ) G ( x H z ) ) )
  assume isringod.6: |- ( ( ph /\ ( x e. X /\ y e. X /\ z e. X ) ) -> ( ( x G y ) H z ) = ( ( x H z ) G ( y H z ) ) )
  assume isringod.7: |- ( ph -> U e. X )
  assume isringod.8: |- ( ( ph /\ y e. X ) -> ( U H y ) = y )
  assume isringod.9: |- ( ( ph /\ y e. X ) -> ( y H U ) = y )

  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint U x
  disjoint U y
  assert |- ( ph -> <. G , H >. e. RingOps )

  proof
    wph
    cG
    cH
    cop
    crngo
    wcel
    #
    cG
    cablo
    wcel
    #
    cG
    crn
    #
    @2
    cxp
    #
    @2
    cH
    wf
    #
    wa
    vx
    cv
    #
    vy
    cv
    #
    cH
    co
    #
    vz
    cv
    #
    cH
    co
    @5
    @6
    @8
    cH
    co
    #
    cH
    co
    wceq
    #
    @5
    @6
    @8
    cG
    co
    cH
    co
    @7
    @5
    @8
    cH
    co
    #
    cG
    co
    wceq
    #
    @5
    @6
    cG
    co
    @8
    cH
    co
    @11
    @9
    cG
    co
    wceq
    #
    w3a
    #
    vz
    @2
    wral
    #
    vy
    @2
    wral
    #
    vx
    @2
    wral
    #
    @7
    @6
    wceq
    #
    @6
    @5
    cH
    co
    #
    @6
    wceq
    #
    wa
    #
    vy
    @2
    wral
    #
    vx
    @2
    wrex
    #
    wa
    #
    wa
    #
    wph
    @1
    @4
    @24
    isringod.1
    wph
    cX
    cX
    cxp
    #
    cX
    cH
    wf
    @4
    isringod.3
    wph
    @26
    cX
    @3
    @2
    cH
    wph
    cX
    @2
    isringod.2
    sqxpeqd
    isringod.2
    feq23d
    mpbid
    #
    wph
    @17
    @23
    wph
    @14
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
    @17
    wph
    @14
    vx
    vy
    vz
    cX
    cX
    cX
    wph
    @5
    cX
    wcel
    @6
    cX
    wcel
    #
    @8
    cX
    wcel
    w3a
    wa
    @10
    @12
    @13
    isringod.4
    isringod.5
    isringod.6
    3jca
    ralrimivvva
    wph
    @29
    @16
    vx
    cX
    @2
    isringod.2
    wph
    @28
    @15
    vy
    cX
    @2
    isringod.2
    wph
    @14
    vz
    cX
    @2
    isringod.2
    raleqdv
    raleqbidv
    raleqbidv
    mpbid
    wph
    @21
    vy
    cX
    wral
    #
    vx
    cX
    wrex
    #
    @23
    wph
    cU
    cX
    wcel
    cU
    @6
    cH
    co
    #
    @6
    wceq
    #
    @6
    cU
    cH
    co
    #
    @6
    wceq
    #
    wa
    #
    vy
    cX
    wral
    #
    @32
    isringod.7
    wph
    @37
    vy
    cX
    wph
    @30
    wa
    @34
    @36
    isringod.8
    isringod.9
    jca
    ralrimiva
    @31
    @38
    vx
    cU
    cX
    @5
    cU
    wceq
    #
    @21
    @37
    vy
    cX
    @39
    @18
    @34
    @20
    @36
    @39
    @7
    @33
    @6
    @5
    cU
    @6
    cH
    oveq1
    eqeq1d
    @39
    @19
    @35
    @6
    @5
    cU
    @6
    cH
    oveq2
    eqeq1d
    anbi12d
    ralbidv
    rspcev
    syl2anc
    wph
    @31
    @22
    vx
    cX
    @2
    isringod.2
    wph
    @21
    vy
    cX
    @2
    isringod.2
    raleqdv
    rexeqbidv
    mpbid
    jca
    jca31
    wph
    cH
    cvv
    wcel
    #
    @0
    @25
    wb
    wph
    @4
    @3
    cvv
    wcel
    #
    @40
    @27
    wph
    @2
    cvv
    wcel
    #
    @42
    @41
    wph
    @1
    @42
    isringod.1
    cG
    cablo
    rnexg
    syl
    #
    @43
    @2
    @2
    cvv
    cvv
    xpexg
    syl2anc
    @3
    @2
    cvv
    cH
    fex
    syl2anc
    vx
    vy
    vz
    cvv
    cG
    cH
    @2
    @2
    eqid
    isrngo
    syl
    mpbird
end
