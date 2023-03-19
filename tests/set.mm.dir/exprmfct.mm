include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cprime.mm"
include "wrex.mm"
include "eluz2nn.mm"
include "wi.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "eleq1.mm"
include "imbi1d.mm"
include "breq2.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "cc0.mm"
include "cmin.mm"
include "1m1e0.mm"
include "uz2m1nn.mm"
include "syl5eqelr.mm"
include "0nnn.mm"
include "pm2.21i.mm"
include "syl.mm"
include "cz.mm"
include "prmz.mm"
include "iddvds.mm"
include "breq1.mm"
include "rspcev.mm"
include "mpdan.mm"
include "a1d.mm"
include "wa.mm"
include "simpl.mm"
include "eluzelz.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "dvdsmul1.mm"
include "syl2anc.mm"
include "adantl.mm"
include "zmulcld.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "reximdva.mm"
include "embantd.mm"
include "a1dd.mm"
include "adantrd.mm"
include "prmind.mm"
include "mpcom.mm"

theorem exprmfct
  let cN: class N
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint N p
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint x y
  disjoint x z
  disjoint N x
  disjoint y z
  disjoint N y
  disjoint N z
  assert |- ( N e. ( ZZ>= ` 2 ) -> E. p e. Prime p || N )

  proof
    cN
    cn
    wcel
    cN
    c2
    cuz
    cfv
    #
    wcel
    #
    vp
    cv
    #
    cN
    cdvds
    wbr
    #
    vp
    cprime
    wrex
    #
    cN
    eluz2nn
    vx
    cv
    #
    @0
    wcel
    #
    @2
    @5
    cdvds
    wbr
    #
    vp
    cprime
    wrex
    #
    wi
    c1
    @0
    wcel
    #
    @8
    wi
    vy
    cv
    #
    @0
    wcel
    #
    @2
    @10
    cdvds
    wbr
    #
    vp
    cprime
    wrex
    #
    wi
    #
    vz
    cv
    #
    @0
    wcel
    #
    @2
    @15
    cdvds
    wbr
    #
    vp
    cprime
    wrex
    #
    wi
    #
    @10
    @15
    cmul
    co
    #
    @0
    wcel
    #
    @2
    @20
    cdvds
    wbr
    #
    vp
    cprime
    wrex
    #
    wi
    #
    @1
    @4
    wi
    vx
    vy
    vz
    cN
    @5
    c1
    wceq
    @6
    @9
    @8
    @5
    c1
    @0
    eleq1
    imbi1d
    @5
    @10
    wceq
    #
    @6
    @11
    @8
    @13
    @5
    @10
    @0
    eleq1
    @25
    @7
    @12
    vp
    cprime
    @5
    @10
    @2
    cdvds
    breq2
    rexbidv
    imbi12d
    @5
    @15
    wceq
    #
    @6
    @16
    @8
    @18
    @5
    @15
    @0
    eleq1
    @26
    @7
    @17
    vp
    cprime
    @5
    @15
    @2
    cdvds
    breq2
    rexbidv
    imbi12d
    @5
    @20
    wceq
    #
    @6
    @21
    @8
    @23
    @5
    @20
    @0
    eleq1
    @27
    @7
    @22
    vp
    cprime
    @5
    @20
    @2
    cdvds
    breq2
    rexbidv
    imbi12d
    @5
    cN
    wceq
    #
    @6
    @1
    @8
    @4
    @5
    cN
    @0
    eleq1
    @28
    @7
    @3
    vp
    cprime
    @5
    cN
    @2
    cdvds
    breq2
    rexbidv
    imbi12d
    @9
    cc0
    cn
    wcel
    #
    @8
    @9
    cc0
    c1
    c1
    cmin
    co
    cn
    1m1e0
    c1
    uz2m1nn
    syl5eqelr
    @29
    @8
    0nnn
    pm2.21i
    syl
    @5
    cprime
    wcel
    #
    @8
    @6
    @30
    @5
    @5
    cdvds
    wbr
    #
    @8
    @30
    @5
    cz
    wcel
    @31
    @5
    prmz
    @5
    iddvds
    syl
    @7
    @31
    vp
    @5
    cprime
    @2
    @5
    @5
    cdvds
    breq1
    rspcev
    mpdan
    a1d
    @11
    @16
    wa
    #
    @14
    @24
    @19
    @32
    @14
    @23
    @21
    @32
    @11
    @13
    @23
    @11
    @16
    simpl
    @32
    @12
    @22
    vp
    cprime
    @32
    @2
    cprime
    wcel
    #
    wa
    #
    @12
    @10
    @20
    cdvds
    wbr
    #
    @22
    @34
    @10
    cz
    wcel
    #
    @15
    cz
    wcel
    #
    @35
    @11
    @36
    @16
    @33
    c2
    @10
    eluzelz
    ad2antrr
    #
    @16
    @37
    @11
    @33
    c2
    @15
    eluzelz
    ad2antlr
    #
    @10
    @15
    dvdsmul1
    syl2anc
    @34
    @2
    cz
    wcel
    #
    @36
    @20
    cz
    wcel
    @12
    @35
    wa
    @22
    wi
    @33
    @40
    @32
    @2
    prmz
    adantl
    @38
    @34
    @10
    @15
    @38
    @39
    zmulcld
    @2
    @10
    @20
    dvdstr
    syl3anc
    mpan2d
    reximdva
    embantd
    a1dd
    adantrd
    prmind
    mpcom
end
