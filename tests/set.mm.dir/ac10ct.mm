include "cv.mm"
include "cdom.mm"
include "wbr.mm"
include "wwe.mm"
include "wex.mm"
include "con0.mm"
include "wcel.mm"
include "wi.mm"
include "wf1.mm"
include "wa.mm"
include "vex.mm"
include "brdom.mm"
include "crn.mm"
include "cep.mm"
include "wss.mm"
include "wf.mm"
include "f1f.mm"
include "frn.mm"
include "syl.mm"
include "onss.mm"
include "sstr2.mm"
include "syl2im.mm"
include "epweon.mm"
include "wess.mm"
include "syl6mpi.mm"
include "adantl.mm"
include "cfv.mm"
include "copab.mm"
include "wf1o.mm"
include "f1f1orn.mm"
include "eqid.mm"
include "f1owe.mm"
include "cxp.mm"
include "cin.mm"
include "weinxp.mm"
include "cvv.mm"
include "reldom.mm"
include "brrelexi.mm"
include "sqxpexg.mm"
include "incom.mm"
include "inex1g.mm"
include "syl5eqelr.mm"
include "weeq1.mm"
include "spcegv.mm"
include "4syl.mm"
include "syl5bi.mm"
include "sylan9r.mm"
include "syld.mm"
include "impancom.mm"
include "exlimdv.mm"
include "ex.mm"
include "pm2.43b.mm"
include "rexlimiv.mm"

theorem ac10ct
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let vw: setvar w
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint A f
  disjoint f x
  disjoint f y
  disjoint f w
  disjoint f z
  disjoint w x
  disjoint w z
  disjoint x z
  assert |- ( E. y e. On A ~<_ y -> E. x x We A )

  proof
    cA
    vy
    cv
    #
    cdom
    wbr
    #
    cA
    vx
    cv
    #
    wwe
    #
    vx
    wex
    #
    vy
    con0
    @0
    con0
    wcel
    #
    @1
    @4
    @1
    @5
    @1
    @4
    wi
    @1
    cA
    @0
    vf
    cv
    #
    wf1
    #
    vf
    wex
    @1
    @5
    wa
    #
    @4
    cA
    @0
    vf
    vy
    vex
    brdom
    @8
    @7
    @4
    vf
    @1
    @7
    @5
    @4
    @1
    @7
    wa
    @5
    @6
    crn
    #
    cep
    wwe
    #
    @4
    @7
    @5
    @10
    wi
    @1
    @7
    @5
    @9
    con0
    wss
    #
    con0
    cep
    wwe
    @10
    @7
    @9
    @0
    wss
    #
    @5
    @0
    con0
    wss
    @11
    @7
    cA
    @0
    @6
    wf
    @12
    cA
    @0
    @6
    f1f
    cA
    @0
    @6
    frn
    syl
    @0
    onss
    @9
    @0
    con0
    sstr2
    syl2im
    epweon
    @9
    con0
    cep
    wess
    syl6mpi
    adantl
    @7
    @10
    cA
    vw
    cv
    @6
    cfv
    vz
    cv
    @6
    cfv
    cep
    wbr
    vw
    vz
    copab
    #
    wwe
    #
    @1
    @4
    @7
    cA
    @9
    @6
    wf1o
    @10
    @14
    wi
    cA
    @0
    @6
    f1f1orn
    vw
    vz
    cA
    @9
    @13
    cep
    @6
    @13
    eqid
    f1owe
    syl
    @14
    cA
    @13
    cA
    cA
    cxp
    #
    cin
    #
    wwe
    #
    @1
    @4
    cA
    @13
    weinxp
    @1
    cA
    cvv
    wcel
    @15
    cvv
    wcel
    #
    @16
    cvv
    wcel
    @17
    @4
    wi
    cA
    @0
    cdom
    reldom
    brrelexi
    cA
    cvv
    sqxpexg
    @18
    @16
    @15
    @13
    cin
    cvv
    @15
    @13
    incom
    @15
    @13
    cvv
    inex1g
    syl5eqelr
    @3
    @17
    vx
    @16
    cvv
    cA
    @2
    @16
    weeq1
    spcegv
    4syl
    syl5bi
    sylan9r
    syld
    impancom
    exlimdv
    syl5bi
    ex
    pm2.43b
    rexlimiv
end
