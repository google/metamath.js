include "cpo.mm"
include "wcel.mm"
include "wa.mm"
include "cress.mm"
include "co.mm"
include "cvv.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "w3a.mm"
include "cbs.mm"
include "wral.mm"
include "ovexd.mm"
include "wss.mm"
include "cin.mm"
include "eqid.mm"
include "ressbas.mm"
include "inss2.mm"
include "syl6eqssr.mm"
include "adantl.mm"
include "ispos.mm"
include "simprbi.mm"
include "adantr.mm"
include "ssralv.mm"
include "ralimdv.mm"
include "syld.mm"
include "sylc.mm"
include "wb.mm"
include "ressle.mm"
include "breq.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "imbi12d.mm"
include "3anbi123d.mm"
include "ralbidv.mm"
include "2ralbidv.mm"
include "syl.mm"
include "mpbid.mm"
include "sylanbrc.mm"

theorem resspos
  let cA: class A
  let cF: class F
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( F e. Poset /\ A e. V ) -> ( F |`s A ) e. Poset )

  proof
    cF
    cpo
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
    cvv
    wcel
    vx
    cv
    #
    @4
    @3
    cple
    cfv
    #
    wbr
    #
    @4
    vy
    cv
    #
    @5
    wbr
    #
    @7
    @4
    @5
    wbr
    #
    wa
    #
    @4
    @7
    wceq
    #
    wi
    #
    @8
    @7
    vz
    cv
    #
    @5
    wbr
    #
    wa
    #
    @4
    @13
    @5
    wbr
    #
    wi
    #
    w3a
    #
    vz
    @3
    cbs
    cfv
    #
    wral
    #
    vy
    @19
    wral
    vx
    @19
    wral
    #
    @3
    cpo
    wcel
    @2
    cF
    cA
    cress
    ovexd
    @2
    @4
    @4
    cF
    cple
    cfv
    #
    wbr
    #
    @4
    @7
    @22
    wbr
    #
    @7
    @4
    @22
    wbr
    #
    wa
    #
    @11
    wi
    #
    @24
    @7
    @13
    @22
    wbr
    #
    wa
    #
    @4
    @13
    @22
    wbr
    #
    wi
    #
    w3a
    #
    vz
    @19
    wral
    #
    vy
    @19
    wral
    #
    vx
    @19
    wral
    #
    @21
    @2
    @19
    cF
    cbs
    cfv
    #
    wss
    #
    @32
    vz
    @36
    wral
    #
    vy
    @36
    wral
    #
    vx
    @36
    wral
    #
    @35
    @1
    @37
    @0
    @1
    @19
    cA
    @36
    cin
    @36
    cA
    @36
    @3
    cV
    cF
    @3
    eqid
    #
    @36
    eqid
    #
    ressbas
    cA
    @36
    inss2
    syl6eqssr
    adantl
    @0
    @40
    @1
    @0
    cF
    cvv
    wcel
    @40
    vx
    vy
    vz
    @36
    cF
    @22
    @42
    @22
    eqid
    #
    ispos
    simprbi
    adantr
    @37
    @40
    @34
    vx
    @36
    wral
    @35
    @37
    @39
    @34
    vx
    @36
    @37
    @39
    @33
    vy
    @36
    wral
    @34
    @37
    @38
    @33
    vy
    @36
    @32
    vz
    @19
    @36
    ssralv
    ralimdv
    @33
    vy
    @19
    @36
    ssralv
    syld
    ralimdv
    @34
    vx
    @19
    @36
    ssralv
    syld
    sylc
    @2
    @22
    @5
    wceq
    #
    @35
    @21
    wb
    @1
    @44
    @0
    cA
    cF
    @22
    cV
    @3
    @41
    @43
    ressle
    adantl
    @44
    @33
    @20
    vx
    vy
    @19
    @19
    @44
    @32
    @18
    vz
    @19
    @44
    @23
    @6
    @27
    @12
    @31
    @17
    @4
    @4
    @22
    @5
    breq
    @44
    @26
    @10
    @11
    @44
    @24
    @8
    @25
    @9
    @4
    @7
    @22
    @5
    breq
    #
    @7
    @4
    @22
    @5
    breq
    anbi12d
    imbi1d
    @44
    @29
    @15
    @30
    @16
    @44
    @24
    @8
    @28
    @14
    @45
    @7
    @13
    @22
    @5
    breq
    anbi12d
    @4
    @13
    @22
    @5
    breq
    imbi12d
    3anbi123d
    ralbidv
    2ralbidv
    syl
    mpbid
    vx
    vy
    vz
    @19
    @3
    @5
    @19
    eqid
    @5
    eqid
    ispos
    sylanbrc
end
