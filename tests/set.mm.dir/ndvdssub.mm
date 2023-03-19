include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cdvds.mm"
include "cmin.mm"
include "co.mm"
include "wn.mm"
include "wi.mm"
include "w3a.mm"
include "cn0.mm"
include "cc0.mm"
include "wne.mm"
include "nnnn0.mm"
include "nnne0.mm"
include "jca.mm"
include "wceq.mm"
include "df-ne.mm"
include "anbi2i.mm"
include "cv.mm"
include "wral.mm"
include "wrex.mm"
include "wreu.mm"
include "divalg2.mm"
include "breq1.mm"
include "oveq2.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "reu4.mm"
include "sylib.mm"
include "nngt0.mm"
include "3ad2ant2.mm"
include "zcn.mm"
include "subid1d.mm"
include "biimpar.mm"
include "3adant2.mm"
include "3expa.mm"
include "anim2i.mm"
include "ancoms.mm"
include "0nn0.mm"
include "anbi2d.mm"
include "eqeq2.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "ax-mp.mm"
include "syl5.mm"
include "expd.mm"
include "ralimi.mm"
include "simpl2im.mm"
include "r19.21v.mm"
include "pm2.43i.mm"
include "3impia.mm"
include "eqeq1.mm"
include "syl5com.mm"
include "pm4.14.mm"
include "syl6ib.mm"
include "syl7bi.mm"
include "exp4a.mm"
include "com23.mm"
include "imp4a.mm"
include "syl7.mm"
include "impd.mm"
include "3expia.mm"

theorem ndvdssub
  let cD: class D
  let cK: class K
  let cN: class N
  let vr: setvar r
  let vx: setvar x


  assert |- ( ( N e. ZZ /\ D e. NN /\ ( K e. NN /\ K < D ) ) -> ( D || N -> -. D || ( N - K ) ) )

  proof
    cN
    cz
    wcel
    #
    cD
    cn
    wcel
    #
    cK
    cn
    wcel
    #
    cK
    cD
    clt
    wbr
    #
    wa
    #
    cD
    cN
    cdvds
    wbr
    #
    cD
    cN
    cK
    cmin
    co
    #
    cdvds
    wbr
    #
    wn
    #
    wi
    @0
    @1
    wa
    #
    @5
    @4
    @8
    @0
    @1
    @5
    @4
    @8
    wi
    @0
    @1
    @5
    w3a
    #
    @2
    @3
    @8
    @10
    @3
    @2
    @8
    @2
    cK
    cn0
    wcel
    #
    cK
    cc0
    wne
    #
    wa
    @10
    @3
    @8
    @2
    @11
    @12
    cK
    nnnn0
    cK
    nnne0
    jca
    @10
    @3
    @11
    @12
    @8
    @10
    @11
    @3
    @12
    @8
    wi
    @10
    @11
    @3
    @12
    @8
    @3
    @12
    wa
    @3
    cK
    cc0
    wceq
    #
    wn
    #
    wa
    #
    @10
    @11
    @8
    @12
    @14
    @3
    cK
    cc0
    df-ne
    anbi2i
    @10
    @11
    @3
    @7
    wa
    #
    @13
    wi
    #
    @15
    @8
    wi
    @10
    vr
    cv
    #
    cD
    clt
    wbr
    #
    cD
    cN
    @18
    cmin
    co
    #
    cdvds
    wbr
    #
    wa
    #
    @18
    cc0
    wceq
    #
    wi
    #
    vr
    cn0
    wral
    #
    @11
    @17
    @0
    @1
    @5
    @25
    @9
    @5
    @25
    wi
    @9
    @9
    @5
    @25
    @9
    @9
    @5
    wa
    #
    @24
    wi
    #
    vr
    cn0
    wral
    #
    @26
    @25
    wi
    @9
    @22
    vr
    cn0
    wrex
    #
    @22
    vx
    cv
    #
    cD
    clt
    wbr
    #
    cD
    cN
    @30
    cmin
    co
    #
    cdvds
    wbr
    #
    wa
    #
    wa
    #
    @18
    @30
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    vr
    cn0
    wral
    #
    @28
    @9
    @22
    vr
    cn0
    wreu
    @29
    @39
    wa
    cD
    cN
    vr
    divalg2
    @22
    @34
    vr
    vx
    cn0
    @36
    @19
    @31
    @21
    @33
    @18
    @30
    cD
    clt
    breq1
    @36
    @20
    @32
    cD
    cdvds
    @18
    @30
    cN
    cmin
    oveq2
    breq2d
    anbi12d
    reu4
    sylib
    @38
    @27
    vr
    cn0
    @38
    @26
    @22
    @23
    @26
    @22
    wa
    @22
    cc0
    cD
    clt
    wbr
    #
    cD
    cN
    cc0
    cmin
    co
    #
    cdvds
    wbr
    #
    wa
    #
    wa
    #
    @38
    @23
    @22
    @26
    @44
    @26
    @43
    @22
    @0
    @1
    @5
    @43
    @10
    @40
    @42
    @1
    @0
    @40
    @5
    cD
    nngt0
    3ad2ant2
    @0
    @5
    @42
    @1
    @0
    @42
    @5
    @0
    @41
    cN
    cD
    cdvds
    @0
    cN
    cN
    zcn
    subid1d
    breq2d
    biimpar
    3adant2
    jca
    3expa
    anim2i
    ancoms
    cc0
    cn0
    wcel
    @38
    @44
    @23
    wi
    #
    wi
    0nn0
    @37
    @45
    vx
    cc0
    cn0
    @30
    cc0
    wceq
    #
    @35
    @44
    @36
    @23
    @46
    @34
    @43
    @22
    @46
    @31
    @40
    @33
    @42
    @30
    cc0
    cD
    clt
    breq1
    @46
    @32
    @41
    cD
    cdvds
    @30
    cc0
    cN
    cmin
    oveq2
    breq2d
    anbi12d
    anbi2d
    @30
    cc0
    @18
    eqeq2
    imbi12d
    rspcv
    ax-mp
    syl5
    expd
    ralimi
    simpl2im
    @26
    @24
    vr
    cn0
    r19.21v
    sylib
    expd
    pm2.43i
    3impia
    @24
    @17
    vr
    cK
    cn0
    @18
    cK
    wceq
    #
    @22
    @16
    @23
    @13
    @47
    @19
    @3
    @21
    @7
    @18
    cK
    cD
    clt
    breq1
    @47
    @20
    @6
    cD
    cdvds
    @18
    cK
    cN
    cmin
    oveq2
    breq2d
    anbi12d
    @18
    cK
    cc0
    eqeq1
    imbi12d
    rspcv
    syl5com
    @3
    @7
    @13
    pm4.14
    syl6ib
    syl7bi
    exp4a
    com23
    imp4a
    syl7
    com23
    impd
    3expia
    com23
    3impia
end
