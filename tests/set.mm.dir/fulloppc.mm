include "ctpos.mm"
include "cfunc.mm"
include "co.mm"
include "wbr.mm"
include "cv.mm"
include "crn.mm"
include "cfv.mm"
include "chom.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "cful.mm"
include "fullfunc.mm"
include "ssbri.mm"
include "syl.mm"
include "funcoppc.mm"
include "wcel.mm"
include "wa.mm"
include "wfo.mm"
include "eqid.mm"
include "adantr.mm"
include "simprr.mm"
include "simprl.mm"
include "fullfo.mm"
include "forn.mm"
include "ovtpos.mm"
include "rneqi.mm"
include "oppchom.mm"
include "3eqtr4g.mm"
include "ralrimivva.mm"
include "oppcbas.mm"
include "isfull.mm"
include "sylanbrc.mm"

theorem fulloppc
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cP: class P
  let cF: class F
  let cG: class G
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  assume fulloppc.o: |- O = ( oppCat ` C )
  assume fulloppc.p: |- P = ( oppCat ` D )
  assume fulloppc.f: |- ( ph -> F ( C Full D ) G )


  assert |- ( ph -> F ( O Full P ) tpos G )

  proof
    wph
    cF
    cG
    ctpos
    #
    cO
    cP
    cfunc
    co
    wbr
    vx
    cv
    #
    vy
    cv
    #
    @0
    co
    #
    crn
    #
    @1
    cF
    cfv
    #
    @2
    cF
    cfv
    #
    cP
    chom
    cfv
    #
    co
    #
    wceq
    #
    vy
    cC
    cbs
    cfv
    #
    wral
    vx
    @10
    wral
    cF
    @0
    cO
    cP
    cful
    co
    wbr
    wph
    cC
    cD
    cP
    cF
    cG
    cO
    fulloppc.o
    fulloppc.p
    wph
    cF
    cG
    cC
    cD
    cful
    co
    #
    wbr
    #
    cF
    cG
    cC
    cD
    cfunc
    co
    #
    wbr
    fulloppc.f
    @11
    @13
    cF
    cG
    cC
    cD
    fullfunc
    ssbri
    syl
    funcoppc
    wph
    @9
    vx
    vy
    @10
    @10
    wph
    @1
    @10
    wcel
    #
    @2
    @10
    wcel
    #
    wa
    #
    wa
    #
    @2
    @1
    cG
    co
    #
    crn
    #
    @6
    @5
    cD
    chom
    cfv
    #
    co
    #
    @4
    @8
    @17
    @2
    @1
    cC
    chom
    cfv
    #
    co
    #
    @21
    @18
    wfo
    @19
    @21
    wceq
    @17
    @10
    cC
    cD
    cF
    cG
    @22
    @20
    @2
    @1
    @10
    eqid
    #
    @20
    eqid
    #
    @22
    eqid
    wph
    @12
    @16
    fulloppc.f
    adantr
    wph
    @14
    @15
    simprr
    wph
    @14
    @15
    simprl
    fullfo
    @23
    @21
    @18
    forn
    syl
    @3
    @18
    @1
    @2
    cG
    ovtpos
    rneqi
    cD
    @20
    cP
    @5
    @6
    @25
    fulloppc.p
    oppchom
    3eqtr4g
    ralrimivva
    vx
    vy
    @10
    cO
    cP
    cF
    @0
    @7
    @10
    cC
    cO
    fulloppc.o
    @24
    oppcbas
    @7
    eqid
    isfull
    sylanbrc
end
