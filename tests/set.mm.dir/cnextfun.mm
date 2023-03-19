include "ctop.mm"
include "wcel.mm"
include "cha.mm"
include "wa.mm"
include "wf.mm"
include "wss.mm"
include "ccnext.mm"
include "co.mm"
include "cfv.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "wfun.mm"
include "haustop.mm"
include "cnextrel.mm"
include "sylanl2.mm"
include "ccl.mm"
include "csn.mm"
include "cnei.mm"
include "crest.mm"
include "cflf.mm"
include "wi.mm"
include "cfil.mm"
include "simpllr.mm"
include "ctopon.mm"
include "toptopon.mm"
include "biimpi.mm"
include "ad3antrrr.mm"
include "simplrr.mm"
include "sylibr.mm"
include "clsss3.mm"
include "syl2anc.mm"
include "simpr.mm"
include "sseldd.mm"
include "w3a.mm"
include "trnei.mm"
include "biimpa.mm"
include "syl31anc.mm"
include "simplrl.mm"
include "hausflf.mm"
include "syl3anc.mm"
include "ex.mm"
include "alrimiv.mm"
include "moanimv.mm"
include "albii.mm"
include "cop.mm"
include "cxp.mm"
include "ciun.mm"
include "wb.mm"
include "df-br.mm"
include "a1i.mm"
include "wceq.mm"
include "cnextfval.mm"
include "eleq2d.mm"
include "opeliunxp.mm"
include "3bitrd.mm"
include "mobidv.mm"
include "albidv.mm"
include "mpbird.mm"
include "dffun6.mm"
include "sylanbrc.mm"

theorem cnextfun
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cJ: class J
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  assume cnextfrel.1: |- C = U. J
  assume cnextfrel.2: |- B = U. K


  assert |- ( ( ( J e. Top /\ K e. Haus ) /\ ( F : A --> B /\ A C_ C ) ) -> Fun ( ( J CnExt K ) ` F ) )

  proof
    cJ
    ctop
    wcel
    #
    cK
    cha
    wcel
    #
    wa
    #
    cA
    cB
    cF
    wf
    #
    cA
    cC
    wss
    #
    wa
    #
    wa
    #
    cF
    cJ
    cK
    ccnext
    co
    cfv
    #
    wrel
    #
    vx
    cv
    #
    vy
    cv
    #
    @7
    wbr
    #
    vy
    wmo
    #
    vx
    wal
    #
    @7
    wfun
    @1
    @0
    cK
    ctop
    wcel
    #
    @5
    @8
    cK
    haustop
    #
    cA
    cB
    cC
    cF
    cJ
    cK
    cnextfrel.1
    cnextfrel.2
    cnextrel
    sylanl2
    @6
    @13
    @9
    cA
    cJ
    ccl
    cfv
    cfv
    #
    wcel
    #
    @10
    cF
    cK
    @9
    csn
    #
    cJ
    cnei
    cfv
    cfv
    cA
    crest
    co
    #
    cflf
    co
    cfv
    #
    wcel
    #
    wa
    #
    vy
    wmo
    #
    vx
    wal
    #
    @6
    @17
    @21
    vy
    wmo
    #
    wi
    #
    vx
    wal
    @24
    @6
    @26
    vx
    @6
    @17
    @25
    @6
    @17
    wa
    #
    @1
    @19
    cA
    cfil
    cfv
    wcel
    #
    @3
    @25
    @0
    @1
    @5
    @17
    simpllr
    @27
    cJ
    cC
    ctopon
    cfv
    wcel
    #
    @4
    @9
    cC
    wcel
    #
    @17
    @28
    @0
    @29
    @1
    @5
    @17
    @0
    @29
    cJ
    cC
    cnextfrel.1
    toptopon
    #
    biimpi
    ad3antrrr
    #
    @2
    @3
    @4
    @17
    simplrr
    #
    @27
    @16
    cC
    @9
    @27
    @0
    @4
    @16
    cC
    wss
    @27
    @29
    @0
    @32
    @31
    sylibr
    @33
    cA
    cJ
    cC
    cnextfrel.1
    clsss3
    syl2anc
    @6
    @17
    simpr
    #
    sseldd
    @34
    @29
    @4
    @30
    w3a
    @17
    @28
    cA
    @9
    cJ
    cC
    trnei
    biimpa
    syl31anc
    @2
    @3
    @4
    @17
    simplrl
    vy
    cF
    cK
    @19
    cB
    cA
    cnextfrel.2
    hausflf
    syl3anc
    ex
    alrimiv
    @23
    @26
    vx
    @17
    @21
    vy
    moanimv
    albii
    sylibr
    @6
    @12
    @23
    vx
    @6
    @11
    @22
    vy
    @6
    @11
    @9
    @10
    cop
    #
    @7
    wcel
    #
    @35
    vx
    @16
    @18
    @20
    cxp
    ciun
    #
    wcel
    #
    @22
    @11
    @36
    wb
    @6
    @9
    @10
    @7
    df-br
    a1i
    @6
    @7
    @37
    @35
    @1
    @0
    @14
    @5
    @7
    @37
    wceq
    @15
    vx
    cA
    cB
    cF
    cJ
    cK
    cC
    cnextfrel.1
    cnextfrel.2
    cnextfval
    sylanl2
    eleq2d
    @38
    @22
    wb
    @6
    vx
    @16
    @20
    @10
    opeliunxp
    a1i
    3bitrd
    mobidv
    albidv
    mpbird
    vx
    vy
    @7
    dffun6
    sylanbrc
end
