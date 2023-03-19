include "ctpos.mm"
include "cfunc.mm"
include "co.mm"
include "wbr.mm"
include "cv.mm"
include "ccnv.mm"
include "wfun.mm"
include "cbs.mm"
include "cfv.mm"
include "wral.mm"
include "cfth.mm"
include "fthfunc.mm"
include "ssbri.mm"
include "syl.mm"
include "funcoppc.mm"
include "wcel.mm"
include "wa.mm"
include "chom.mm"
include "wf1.mm"
include "eqid.mm"
include "adantr.mm"
include "simprr.mm"
include "simprl.mm"
include "fthf1.mm"
include "wf.mm"
include "df-f1.mm"
include "simprbi.mm"
include "ovtpos.mm"
include "cnveqi.mm"
include "funeqi.mm"
include "sylibr.mm"
include "ralrimivva.mm"
include "oppcbas.mm"
include "isfth.mm"
include "sylanbrc.mm"

theorem fthoppc
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
  assume fthoppc.f: |- ( ph -> F ( C Faith D ) G )


  assert |- ( ph -> F ( O Faith P ) tpos G )

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
    ccnv
    #
    wfun
    #
    vy
    cC
    cbs
    cfv
    #
    wral
    vx
    @6
    wral
    cF
    @0
    cO
    cP
    cfth
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
    cfth
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
    fthoppc.f
    @7
    @9
    cF
    cG
    cC
    cD
    fthfunc
    ssbri
    syl
    funcoppc
    wph
    @5
    vx
    vy
    @6
    @6
    wph
    @1
    @6
    wcel
    #
    @2
    @6
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
    ccnv
    #
    wfun
    #
    @5
    @13
    @2
    @1
    cC
    chom
    cfv
    #
    co
    #
    @2
    cF
    cfv
    @1
    cF
    cfv
    cD
    chom
    cfv
    #
    co
    #
    @14
    wf1
    #
    @16
    @13
    @6
    cC
    cD
    cF
    cG
    @17
    @19
    @2
    @1
    @6
    eqid
    #
    @17
    eqid
    @19
    eqid
    wph
    @8
    @12
    fthoppc.f
    adantr
    wph
    @10
    @11
    simprr
    wph
    @10
    @11
    simprl
    fthf1
    @21
    @18
    @20
    @14
    wf
    @16
    @18
    @20
    @14
    df-f1
    simprbi
    syl
    @4
    @15
    @3
    @14
    @1
    @2
    cG
    ovtpos
    cnveqi
    funeqi
    sylibr
    ralrimivva
    vx
    vy
    @6
    cO
    cP
    cF
    @0
    @6
    cC
    cO
    fulloppc.o
    @22
    oppcbas
    isfth
    sylanbrc
end
