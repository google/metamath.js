include "crli.mm"
include "wbr.mm"
include "cres.mm"
include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wi.mm"
include "cdm.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "crp.mm"
include "wa.mm"
include "cin.mm"
include "wss.mm"
include "inss1.mm"
include "ssralv.mm"
include "ax-mp.mm"
include "reximi.mm"
include "ralimi.mm"
include "anim2i.mm"
include "a1i.mm"
include "rlimf.mm"
include "rlimss.mm"
include "eqidd.mm"
include "rlim.mm"
include "wf.mm"
include "fssres.mm"
include "sylancl.mm"
include "resres.mm"
include "wfn.mm"
include "wceq.mm"
include "ffn.mm"
include "fnresdm.mm"
include "3syl.mm"
include "reseq1d.mm"
include "syl5eqr.mm"
include "feq1d.mm"
include "mpbid.mm"
include "syl5ss.mm"
include "inss2.mm"
include "sseli.mm"
include "fvres.mm"
include "syl.mm"
include "adantl.mm"
include "3imtr4d.mm"
include "pm2.43i.mm"

theorem rlimres
  let cA: class A
  let cB: class B
  let cF: class F
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( F ~~>r A -> ( F |` B ) ~~>r A )

  proof
    cF
    cA
    crli
    wbr
    #
    cF
    cB
    cres
    #
    cA
    crli
    wbr
    #
    @0
    cA
    cc
    wcel
    #
    vy
    cv
    vz
    cv
    #
    cle
    wbr
    @4
    cF
    cfv
    #
    cA
    cmin
    co
    cabs
    cfv
    vx
    cv
    clt
    wbr
    wi
    #
    vz
    cF
    cdm
    #
    wral
    #
    vy
    cr
    wrex
    #
    vx
    crp
    wral
    #
    wa
    #
    @3
    @6
    vz
    @7
    cB
    cin
    #
    wral
    #
    vy
    cr
    wrex
    #
    vx
    crp
    wral
    #
    wa
    #
    @0
    @2
    @11
    @16
    wi
    @0
    @10
    @15
    @3
    @9
    @14
    vx
    crp
    @8
    @13
    vy
    cr
    @12
    @7
    wss
    #
    @8
    @13
    wi
    @7
    cB
    inss1
    #
    @6
    vz
    @12
    @7
    ssralv
    ax-mp
    reximi
    ralimi
    anim2i
    a1i
    @0
    vx
    vy
    vz
    @7
    @5
    cA
    cF
    cA
    cF
    rlimf
    #
    cA
    cF
    rlimss
    #
    @0
    @4
    @7
    wcel
    wa
    @5
    eqidd
    rlim
    @0
    vx
    vy
    vz
    @12
    @5
    cA
    @1
    @0
    @12
    cc
    cF
    @12
    cres
    #
    wf
    #
    @12
    cc
    @1
    wf
    @0
    @7
    cc
    cF
    wf
    #
    @17
    @22
    @19
    @18
    @7
    cc
    @12
    cF
    fssres
    sylancl
    @0
    @12
    cc
    @21
    @1
    @0
    @21
    cF
    @7
    cres
    #
    cB
    cres
    @1
    cF
    @7
    cB
    resres
    @0
    @24
    cF
    cB
    @0
    @23
    cF
    @7
    wfn
    @24
    cF
    wceq
    @19
    @7
    cc
    cF
    ffn
    @7
    cF
    fnresdm
    3syl
    reseq1d
    syl5eqr
    feq1d
    mpbid
    @0
    @12
    @7
    cr
    @18
    @20
    syl5ss
    @4
    @12
    wcel
    #
    @4
    @1
    cfv
    @5
    wceq
    #
    @0
    @25
    @4
    cB
    wcel
    @26
    @12
    cB
    @4
    @7
    cB
    inss2
    sseli
    @4
    cB
    cF
    fvres
    syl
    adantl
    rlim
    3imtr4d
    pm2.43i
end
