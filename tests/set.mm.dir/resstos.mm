include "ctos.mm"
include "wcel.mm"
include "wa.mm"
include "cress.mm"
include "co.mm"
include "cpo.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wo.mm"
include "cbs.mm"
include "wral.mm"
include "tospos.mm"
include "resspos.mm"
include "sylan.mm"
include "wss.mm"
include "cin.mm"
include "eqid.mm"
include "ressbas.mm"
include "inss2.mm"
include "syl6eqssr.mm"
include "adantl.mm"
include "istos.mm"
include "simprbi.mm"
include "adantr.mm"
include "ssralv.mm"
include "ralimdv.mm"
include "syld.mm"
include "sylc.mm"
include "wb.mm"
include "ressle.mm"
include "breqd.mm"
include "orbi12d.mm"
include "2ralbidv.mm"
include "mpbid.mm"
include "sylanbrc.mm"

theorem resstos
  let cA: class A
  let cF: class F
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( F e. Toset /\ A e. V ) -> ( F |`s A ) e. Toset )

  proof
    cF
    ctos
    wcel
    #
    cA
    cV
    wcel
    #
    wa
    #
    cF
    cA
    cress
    co
    #
    cpo
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    @3
    cple
    cfv
    #
    wbr
    #
    @6
    @5
    @7
    wbr
    #
    wo
    #
    vy
    @3
    cbs
    cfv
    #
    wral
    vx
    @11
    wral
    #
    @3
    ctos
    wcel
    @0
    cF
    cpo
    wcel
    #
    @1
    @4
    cF
    tospos
    cA
    cF
    cV
    resspos
    sylan
    @2
    @5
    @6
    cF
    cple
    cfv
    #
    wbr
    #
    @6
    @5
    @14
    wbr
    #
    wo
    #
    vy
    @11
    wral
    #
    vx
    @11
    wral
    #
    @12
    @2
    @11
    cF
    cbs
    cfv
    #
    wss
    #
    @17
    vy
    @20
    wral
    #
    vx
    @20
    wral
    #
    @19
    @1
    @21
    @0
    @1
    @11
    cA
    @20
    cin
    @20
    cA
    @20
    @3
    cV
    cF
    @3
    eqid
    #
    @20
    eqid
    #
    ressbas
    cA
    @20
    inss2
    syl6eqssr
    adantl
    @0
    @23
    @1
    @0
    @13
    @23
    vx
    vy
    @20
    cF
    @14
    @25
    @14
    eqid
    #
    istos
    simprbi
    adantr
    @21
    @23
    @22
    vx
    @11
    wral
    @19
    @22
    vx
    @11
    @20
    ssralv
    @21
    @22
    @18
    vx
    @11
    @17
    vy
    @11
    @20
    ssralv
    ralimdv
    syld
    sylc
    @1
    @19
    @12
    wb
    @0
    @1
    @17
    @10
    vx
    vy
    @11
    @11
    @1
    @15
    @8
    @16
    @9
    @1
    @14
    @7
    @5
    @6
    cA
    cF
    @14
    cV
    @3
    @24
    @26
    ressle
    #
    breqd
    @1
    @14
    @7
    @6
    @5
    @27
    breqd
    orbi12d
    2ralbidv
    adantl
    mpbid
    vx
    vy
    @11
    @3
    @7
    @11
    eqid
    @7
    eqid
    istos
    sylanbrc
end
