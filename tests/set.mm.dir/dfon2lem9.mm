include "cv.mm"
include "wpss.mm"
include "wtr.mm"
include "wa.mm"
include "wel.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wn.mm"
include "wrex.mm"
include "cep.mm"
include "wfr.mm"
include "ssralv.mm"
include "cint.mm"
include "wcel.mm"
include "dfon2lem8.mm"
include "simprd.mm"
include "intss1.mm"
include "simpld.mm"
include "cvv.mm"
include "intex.mm"
include "wceq.mm"
include "dfon2lem3.mm"
include "imp.mm"
include "untelirr.mm"
include "syl.mm"
include "eleq1.mm"
include "notbid.mm"
include "syl5ibcom.mm"
include "a1dd.mm"
include "trss.mm"
include "eqss.mm"
include "simplbi2com.mm"
include "syl6.mm"
include "com23.mm"
include "con3.mm"
include "pm2.61d.mm"
include "sylanb.mm"
include "syldan.mm"
include "syl5.mm"
include "ralrimiv.mm"
include "eleq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "expcom.mm"
include "syl6com.mm"
include "impd.mm"
include "alrimiv.mm"
include "wbr.mm"
include "df-fr.mm"
include "epel.mm"
include "notbii.mm"
include "ralbii.mm"
include "rexbii.mm"
include "imbi2i.mm"
include "albii.mm"
include "bitri.mm"
include "sylibr.mm"

theorem dfon2lem9
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let vw: setvar w
  let vt: setvar t
  let vu: setvar u

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint A z
  disjoint A w
  disjoint A t
  disjoint A u
  disjoint x z
  disjoint w x
  disjoint t x
  disjoint u x
  disjoint y z
  disjoint w y
  disjoint t y
  disjoint u y
  disjoint w z
  disjoint t z
  disjoint u z
  disjoint t w
  disjoint u w
  disjoint t u
  assert |- ( A. x e. A A. y ( ( y C. x /\ Tr y ) -> y e. x ) -> _E Fr A )

  proof
    vy
    cv
    #
    vx
    cv
    wpss
    @0
    wtr
    wa
    vy
    vx
    wel
    wi
    vy
    wal
    #
    vx
    cA
    wral
    #
    vz
    cv
    #
    cA
    wss
    #
    @3
    c0
    wne
    #
    wa
    #
    vt
    vw
    wel
    #
    wn
    #
    vt
    @3
    wral
    #
    vw
    @3
    wrex
    #
    wi
    #
    vz
    wal
    #
    cA
    cep
    wfr
    #
    @2
    @11
    vz
    @2
    @4
    @5
    @10
    @4
    @2
    @1
    vx
    @3
    wral
    #
    @5
    @10
    wi
    @1
    vx
    @3
    cA
    ssralv
    @5
    @14
    @10
    @5
    @14
    wa
    #
    @3
    cint
    #
    @3
    wcel
    #
    vt
    cv
    #
    @16
    wcel
    #
    wn
    #
    vt
    @3
    wral
    #
    @10
    @15
    vu
    cv
    #
    @16
    wpss
    @22
    wtr
    wa
    @22
    @16
    wcel
    wi
    vu
    wal
    #
    @17
    vx
    vy
    vu
    @3
    dfon2lem8
    #
    simprd
    @15
    @20
    vt
    @3
    vt
    vz
    wel
    @16
    @18
    wss
    #
    @15
    @20
    @18
    @3
    intss1
    @5
    @14
    @23
    @25
    @20
    wi
    #
    @15
    @23
    @17
    @24
    simpld
    @5
    @16
    cvv
    wcel
    #
    @23
    @26
    @3
    intex
    @27
    @23
    wa
    #
    @16
    @18
    wceq
    #
    @26
    @28
    @29
    @20
    @25
    @28
    @16
    @16
    wcel
    #
    wn
    #
    @29
    @20
    @28
    vx
    vx
    wel
    wn
    vx
    @16
    wral
    #
    @31
    @28
    @16
    wtr
    #
    @32
    @27
    @23
    @33
    @32
    wa
    vu
    vx
    @16
    cvv
    dfon2lem3
    imp
    #
    simprd
    vx
    @16
    untelirr
    syl
    @29
    @30
    @19
    @16
    @18
    @16
    eleq1
    notbid
    syl5ibcom
    a1dd
    @28
    @25
    @29
    wn
    #
    @20
    @28
    @25
    @19
    @29
    wi
    @35
    @20
    wi
    @28
    @19
    @25
    @29
    @28
    @19
    @18
    @16
    wss
    #
    @25
    @29
    wi
    @28
    @33
    @19
    @36
    wi
    @28
    @33
    @32
    @34
    simpld
    @16
    @18
    trss
    syl
    @29
    @25
    @36
    @16
    @18
    eqss
    simplbi2com
    syl6
    com23
    @19
    @29
    con3
    syl6
    com23
    pm2.61d
    sylanb
    syldan
    syl5
    ralrimiv
    @9
    @21
    vw
    @16
    @3
    vw
    cv
    #
    @16
    wceq
    #
    @8
    @20
    vt
    @3
    @38
    @7
    @19
    @37
    @16
    @18
    eleq2
    notbid
    ralbidv
    rspcev
    syl2anc
    expcom
    syl6com
    impd
    alrimiv
    @13
    @6
    @18
    @37
    cep
    wbr
    #
    wn
    #
    vt
    @3
    wral
    #
    vw
    @3
    wrex
    #
    wi
    #
    vz
    wal
    @12
    vz
    vw
    vt
    cA
    cep
    df-fr
    @43
    @11
    vz
    @42
    @10
    @6
    @41
    @9
    vw
    @3
    @40
    @8
    vt
    @3
    @39
    @7
    vt
    vw
    epel
    notbii
    ralbii
    rexbii
    imbi2i
    albii
    bitri
    sylibr
end
