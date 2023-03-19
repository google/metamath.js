include "cpreset.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cress.mm"
include "co.mm"
include "cvv.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wi.mm"
include "cbs.mm"
include "wral.mm"
include "ovexd.mm"
include "simp-4l.mm"
include "simp-4r.mm"
include "simpllr.mm"
include "sseldd.mm"
include "jca.mm"
include "simplr.mm"
include "simpr.mm"
include "eqid.mm"
include "isprs.mm"
include "simprbi.mm"
include "r19.21bi.mm"
include "syl21anc.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "ressbas2.mm"
include "adantl.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ssex.mm"
include "ressle.mm"
include "syl.mm"
include "breqd.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "raleqbidv.mm"
include "anbi2d.mm"
include "mpbi2and.mm"
include "sylibr.mm"

theorem ressprs
  let cA: class A
  let cB: class B
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ressprs.b: |- B = ( Base ` K )


  assert |- ( ( K e. Preset /\ A C_ B ) -> ( K |`s A ) e. Preset )

  proof
    cK
    cpreset
    wcel
    #
    cA
    cB
    wss
    #
    wa
    #
    cK
    cA
    cress
    co
    #
    cvv
    wcel
    #
    vx
    cv
    #
    @5
    @3
    cple
    cfv
    #
    wbr
    #
    @5
    vy
    cv
    #
    @6
    wbr
    #
    @8
    vz
    cv
    #
    @6
    wbr
    #
    wa
    #
    @5
    @10
    @6
    wbr
    #
    wi
    #
    wa
    #
    vz
    @3
    cbs
    cfv
    #
    wral
    #
    vy
    @16
    wral
    #
    vx
    @16
    wral
    #
    wa
    #
    @3
    cpreset
    wcel
    @2
    @4
    @5
    @5
    cK
    cple
    cfv
    #
    wbr
    #
    @5
    @8
    @21
    wbr
    #
    @8
    @10
    @21
    wbr
    #
    wa
    #
    @5
    @10
    @21
    wbr
    #
    wi
    #
    wa
    #
    vz
    cA
    wral
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    @20
    @2
    cK
    cA
    cress
    ovexd
    @2
    @30
    vx
    cA
    @2
    @5
    cA
    wcel
    #
    wa
    #
    @29
    vy
    cA
    @33
    @8
    cA
    wcel
    #
    wa
    #
    @28
    vz
    cA
    @35
    @10
    cA
    wcel
    #
    wa
    #
    @0
    @5
    cB
    wcel
    #
    wa
    #
    @8
    cB
    wcel
    #
    @10
    cB
    wcel
    @28
    @37
    @0
    @38
    @0
    @1
    @32
    @34
    @36
    simp-4l
    @37
    cA
    cB
    @5
    @0
    @1
    @32
    @34
    @36
    simp-4r
    #
    @2
    @32
    @34
    @36
    simpllr
    sseldd
    jca
    @37
    cA
    cB
    @8
    @41
    @33
    @34
    @36
    simplr
    sseldd
    @37
    cA
    cB
    @10
    @41
    @35
    @36
    simpr
    sseldd
    @39
    @40
    wa
    @28
    vz
    cB
    @39
    @28
    vz
    cB
    wral
    #
    vy
    cB
    @0
    @42
    vy
    cB
    wral
    #
    vx
    cB
    @0
    cK
    cvv
    wcel
    @43
    vx
    cB
    wral
    vx
    vy
    vz
    cB
    cK
    @21
    ressprs.b
    @21
    eqid
    #
    isprs
    simprbi
    r19.21bi
    r19.21bi
    r19.21bi
    syl21anc
    ralrimiva
    ralrimiva
    ralrimiva
    @2
    @31
    @19
    @4
    @2
    @30
    @18
    vx
    cA
    @16
    @1
    cA
    @16
    wceq
    @0
    cA
    cB
    @3
    cK
    @3
    eqid
    #
    ressprs.b
    ressbas2
    adantl
    #
    @2
    @29
    @17
    vy
    cA
    @16
    @46
    @2
    @28
    @15
    vz
    cA
    @16
    @46
    @2
    @22
    @7
    @27
    @14
    @2
    @21
    @6
    @5
    @5
    @1
    @21
    @6
    wceq
    #
    @0
    @1
    cA
    cvv
    wcel
    @47
    cA
    cB
    cB
    cK
    cbs
    cfv
    cvv
    ressprs.b
    cK
    cbs
    fvex
    eqeltri
    ssex
    cA
    cK
    @21
    cvv
    @3
    @45
    @44
    ressle
    syl
    adantl
    #
    breqd
    @2
    @25
    @12
    @26
    @13
    @2
    @23
    @9
    @24
    @11
    @2
    @21
    @6
    @5
    @8
    @48
    breqd
    @2
    @21
    @6
    @8
    @10
    @48
    breqd
    anbi12d
    @2
    @21
    @6
    @5
    @10
    @48
    breqd
    imbi12d
    anbi12d
    raleqbidv
    raleqbidv
    raleqbidv
    anbi2d
    mpbi2and
    vx
    vy
    vz
    @16
    @3
    @6
    @16
    eqid
    @6
    eqid
    isprs
    sylibr
end
