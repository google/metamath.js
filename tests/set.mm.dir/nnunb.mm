include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "cn.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "wcel.mm"
include "pm3.24.mm"
include "wal.mm"
include "wex.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "peano2rem.mm"
include "ltm1.mm"
include "ovex.mm"
include "eleq1.mm"
include "breq1.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "spcv.mm"
include "syl7.mm"
include "syl5.mm"
include "pm2.43d.mm"
include "df-rex.mm"
include "syl6ib.mm"
include "com12.mm"
include "caddc.mm"
include "wb.mm"
include "nnre.mm"
include "1re.mm"
include "ltsubadd.mm"
include "mp3an2.mm"
include "sylan2.mm"
include "pm5.32da.mm"
include "exbidv.mm"
include "peano2nn.mm"
include "breq2.mm"
include "anbi12d.mm"
include "spcev.mm"
include "sylan.mm"
include "exlimiv.mm"
include "syl6bi.mm"
include "syld.mm"
include "df-ral.mm"
include "alinexa.mm"
include "bitr2i.mm"
include "con1bii.mm"
include "3imtr4g.mm"
include "anim2d.mm"
include "mtoi.mm"
include "nrex.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "nnssre.mm"
include "1nn.mm"
include "n0ii.mm"
include "neir.mm"
include "sup2.mm"
include "mp3an12.mm"
include "mto.mm"

theorem nnunb
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  disjoint y z
  assert |- -. E. x e. RR A. y e. NN ( y < x \/ y = x )

  proof
    vy
    cv
    #
    vx
    cv
    #
    clt
    wbr
    #
    @0
    @1
    wceq
    wo
    vy
    cn
    wral
    vx
    cr
    wrex
    #
    @1
    @0
    clt
    wbr
    #
    wn
    #
    vy
    cn
    wral
    #
    @2
    @0
    vz
    cv
    #
    clt
    wbr
    #
    vz
    cn
    wrex
    #
    wi
    #
    vy
    cr
    wral
    #
    wa
    #
    vx
    cr
    wrex
    #
    @12
    vx
    cr
    @1
    cr
    wcel
    #
    @12
    @6
    @6
    wn
    #
    wa
    @6
    pm3.24
    @14
    @11
    @15
    @6
    @14
    @0
    cr
    wcel
    #
    @10
    wi
    #
    vy
    wal
    #
    @0
    cn
    wcel
    #
    @4
    wa
    #
    vy
    wex
    #
    @11
    @15
    @14
    @18
    @7
    cn
    wcel
    #
    @1
    c1
    cmin
    co
    #
    @7
    clt
    wbr
    #
    wa
    #
    vz
    wex
    #
    @21
    @18
    @14
    @26
    @18
    @14
    @24
    vz
    cn
    wrex
    #
    @26
    @18
    @14
    @27
    @14
    @23
    cr
    wcel
    #
    @18
    @14
    @27
    wi
    @1
    peano2rem
    @14
    @23
    @1
    clt
    wbr
    #
    @18
    @28
    @27
    @1
    ltm1
    @17
    @28
    @29
    @27
    wi
    #
    wi
    vy
    @23
    @1
    c1
    cmin
    ovex
    @0
    @23
    wceq
    #
    @16
    @28
    @10
    @30
    @0
    @23
    cr
    eleq1
    @31
    @2
    @29
    @9
    @27
    @0
    @23
    @1
    clt
    breq1
    @31
    @8
    @24
    vz
    cn
    @0
    @23
    @7
    clt
    breq1
    rexbidv
    imbi12d
    imbi12d
    spcv
    syl7
    syl5
    pm2.43d
    @24
    vz
    cn
    df-rex
    syl6ib
    com12
    @14
    @26
    @22
    @1
    @7
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    vz
    wex
    @21
    @14
    @25
    @34
    vz
    @14
    @22
    @24
    @33
    @22
    @14
    @7
    cr
    wcel
    #
    @24
    @33
    wb
    #
    @7
    nnre
    @14
    c1
    cr
    wcel
    @35
    @36
    1re
    @1
    c1
    @7
    ltsubadd
    mp3an2
    sylan2
    pm5.32da
    exbidv
    @34
    @21
    vz
    @22
    @32
    cn
    wcel
    #
    @33
    @21
    @7
    peano2nn
    @20
    @37
    @33
    wa
    vy
    @32
    @7
    c1
    caddc
    ovex
    @0
    @32
    wceq
    @19
    @37
    @4
    @33
    @0
    @32
    cn
    eleq1
    @0
    @32
    @1
    clt
    breq2
    anbi12d
    spcev
    sylan
    exlimiv
    syl6bi
    syld
    @10
    vy
    cr
    df-ral
    @21
    @6
    @6
    @19
    @5
    wi
    vy
    wal
    @21
    wn
    @5
    vy
    cn
    df-ral
    @19
    @4
    vy
    alinexa
    bitr2i
    con1bii
    3imtr4g
    anim2d
    mtoi
    nrex
    cn
    cr
    wss
    cn
    c0
    wne
    @3
    @13
    nnssre
    cn
    c0
    c1
    cn
    1nn
    n0ii
    neir
    vx
    vy
    vz
    cn
    sup2
    mp3an12
    mto
end
