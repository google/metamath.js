include "c3.mm"
include "cdc.mm"
include "cdvds.mm"
include "wbr.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "c10.mm"
include "c2.mm"
include "cexp.mm"
include "c9.mm"
include "3decOLD.mm"
include "sq10e99m1OLD.mm"
include "oveq1i.mm"
include "9nn0.mm"
include "deccl.mm"
include "nn0cni.mm"
include "ax-1cn.mm"
include "adddiri.mm"
include "mulid2i.mm"
include "oveq2i.mm"
include "3eqtri.mm"
include "df-10OLD.mm"
include "9cn.mm"
include "oveq12i.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "mulcli.mm"
include "wa.mm"
include "add4.mm"
include "oveq1d.mm"
include "mp4an.mm"
include "addcli.mm"
include "addassi.mm"
include "9t11e99.mm"
include "eqcomi.mm"
include "1nn0.mm"
include "mulassi.mm"
include "eqtri.mm"
include "adddii.mm"
include "3t3e9.mm"
include "3cn.mm"
include "breq2i.mm"
include "cz.mm"
include "wb.mm"
include "3z.mm"
include "nn0zi.mm"
include "zaddcl.mm"
include "mp2an.mm"
include "zmulcl.mm"
include "dvdsmul1.mm"
include "pm3.2i.mm"
include "dvdsadd2b.mm"
include "mp3an.mm"
include "bitr4i.mm"

theorem 3dvds2decOLD
  let cA: class A
  let cB: class B
  let cC: class C
  assume 3dvdsdec.a: |- A e. NN0
  assume 3dvdsdec.b: |- B e. NN0
  assume 3dvds2dec.c: |- C e. NN0


  assert |- ( 3 || ; ; A B C <-> 3 || ( ( A + B ) + C ) )

  proof
    c3
    cA
    cB
    cdc
    cC
    cdc
    #
    cdvds
    wbr
    c3
    c3
    c3
    c1
    c1
    cdc
    #
    cA
    cmul
    co
    #
    cB
    caddc
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    cA
    cB
    caddc
    co
    #
    cC
    caddc
    co
    #
    caddc
    co
    #
    cdvds
    wbr
    #
    c3
    @7
    cdvds
    wbr
    #
    @0
    @8
    c3
    cdvds
    @0
    c10
    c2
    cexp
    co
    #
    cA
    cmul
    co
    #
    c10
    cB
    cmul
    co
    #
    caddc
    co
    #
    cC
    caddc
    co
    c9
    c9
    cdc
    #
    cA
    cmul
    co
    #
    cA
    caddc
    co
    #
    c9
    cB
    cmul
    co
    #
    cB
    caddc
    co
    #
    caddc
    co
    #
    cC
    caddc
    co
    #
    @8
    cA
    cB
    cC
    3dvdsdec.a
    3dvdsdec.b
    3decOLD
    @14
    @20
    cC
    caddc
    @12
    @17
    @13
    @19
    caddc
    @12
    @15
    c1
    caddc
    co
    #
    cA
    cmul
    co
    @16
    c1
    cA
    cmul
    co
    #
    caddc
    co
    @17
    @11
    @22
    cA
    cmul
    sq10e99m1OLD
    oveq1i
    @15
    c1
    cA
    @15
    c9
    c9
    9nn0
    9nn0
    deccl
    nn0cni
    #
    ax-1cn
    cA
    3dvdsdec.a
    nn0cni
    #
    adddiri
    @23
    cA
    @16
    caddc
    cA
    @25
    mulid2i
    oveq2i
    3eqtri
    @13
    c9
    c1
    caddc
    co
    #
    cB
    cmul
    co
    @18
    c1
    cB
    cmul
    co
    #
    caddc
    co
    @19
    c10
    @26
    cB
    cmul
    df-10OLD
    oveq1i
    c9
    c1
    cB
    9cn
    ax-1cn
    cB
    3dvdsdec.b
    nn0cni
    #
    adddiri
    @27
    cB
    @18
    caddc
    cB
    @28
    mulid2i
    oveq2i
    3eqtri
    oveq12i
    oveq1i
    @21
    @16
    @18
    caddc
    co
    #
    @6
    caddc
    co
    #
    cC
    caddc
    co
    #
    @29
    @7
    caddc
    co
    @8
    @16
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    @18
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @21
    @31
    wceq
    @15
    cA
    @24
    @25
    mulcli
    #
    @25
    c9
    cB
    9cn
    @28
    mulcli
    #
    @28
    @32
    @33
    wa
    @34
    @35
    wa
    wa
    @20
    @30
    cC
    caddc
    @16
    cA
    @18
    cB
    add4
    oveq1d
    mp4an
    @29
    @6
    cC
    @16
    @18
    @36
    @37
    addcli
    cA
    cB
    @25
    @28
    addcli
    cC
    3dvds2dec.c
    nn0cni
    addassi
    @29
    @5
    @7
    caddc
    @29
    c9
    @2
    cmul
    co
    #
    @18
    caddc
    co
    #
    c9
    @3
    cmul
    co
    #
    @5
    @16
    @38
    @18
    caddc
    @16
    c9
    @1
    cmul
    co
    #
    cA
    cmul
    co
    @38
    @15
    @41
    cA
    cmul
    @41
    @15
    9t11e99
    eqcomi
    oveq1i
    c9
    @1
    cA
    9cn
    @1
    c1
    c1
    1nn0
    1nn0
    deccl
    #
    nn0cni
    #
    @25
    mulassi
    eqtri
    oveq1i
    @40
    @39
    c9
    @2
    cB
    9cn
    @1
    cA
    @43
    @25
    mulcli
    #
    @28
    adddii
    eqcomi
    @40
    c3
    c3
    cmul
    co
    #
    @3
    cmul
    co
    @5
    c9
    @45
    @3
    cmul
    @45
    c9
    3t3e9
    eqcomi
    oveq1i
    c3
    c3
    @3
    3cn
    3cn
    @2
    cB
    @44
    @28
    addcli
    mulassi
    eqtri
    3eqtri
    oveq1i
    3eqtri
    3eqtri
    breq2i
    c3
    cz
    wcel
    #
    @7
    cz
    wcel
    #
    @5
    cz
    wcel
    #
    c3
    @5
    cdvds
    wbr
    #
    wa
    @10
    @9
    wb
    3z
    @6
    cz
    wcel
    #
    cC
    cz
    wcel
    @47
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    @50
    cA
    3dvdsdec.a
    nn0zi
    #
    cB
    3dvdsdec.b
    nn0zi
    #
    cA
    cB
    zaddcl
    mp2an
    cC
    3dvds2dec.c
    nn0zi
    @6
    cC
    zaddcl
    mp2an
    @48
    @49
    @46
    @4
    cz
    wcel
    #
    @48
    3z
    @46
    @3
    cz
    wcel
    #
    @55
    3z
    @2
    cz
    wcel
    #
    @52
    @56
    @1
    cz
    wcel
    @51
    @57
    @1
    @42
    nn0zi
    @53
    @1
    cA
    zmulcl
    mp2an
    @54
    @2
    cB
    zaddcl
    mp2an
    c3
    @3
    zmulcl
    mp2an
    #
    c3
    @4
    zmulcl
    mp2an
    @46
    @55
    @49
    3z
    @58
    c3
    @4
    dvdsmul1
    mp2an
    pm3.2i
    c3
    @7
    @5
    dvdsadd2b
    mp3an
    bitr4i
end
