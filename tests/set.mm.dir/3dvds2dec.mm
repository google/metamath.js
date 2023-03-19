include "c3.mm"
include "cdc.mm"
include "cdvds.mm"
include "wbr.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cc0.mm"
include "c2.mm"
include "cexp.mm"
include "c9.mm"
include "3dec.mm"
include "sq10e99m1.mm"
include "oveq1i.mm"
include "9nn0.mm"
include "deccl.mm"
include "nn0cni.mm"
include "ax-1cn.mm"
include "adddiri.mm"
include "mulid2i.mm"
include "oveq2i.mm"
include "3eqtri.mm"
include "9p1e10.mm"
include "eqcomi.mm"
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

theorem 3dvds2dec
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
    c1
    cc0
    cdc
    #
    c2
    cexp
    co
    #
    cA
    cmul
    co
    #
    @11
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
    3dec
    @15
    @21
    cC
    caddc
    @13
    @18
    @14
    @20
    caddc
    @13
    @16
    c1
    caddc
    co
    #
    cA
    cmul
    co
    @17
    c1
    cA
    cmul
    co
    #
    caddc
    co
    @18
    @12
    @23
    cA
    cmul
    sq10e99m1
    oveq1i
    @16
    c1
    cA
    @16
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
    @24
    cA
    @17
    caddc
    cA
    @26
    mulid2i
    oveq2i
    3eqtri
    @14
    c9
    c1
    caddc
    co
    #
    cB
    cmul
    co
    @19
    c1
    cB
    cmul
    co
    #
    caddc
    co
    @20
    @11
    @27
    cB
    cmul
    @27
    @11
    9p1e10
    eqcomi
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
    @28
    cB
    @19
    caddc
    cB
    @29
    mulid2i
    oveq2i
    3eqtri
    oveq12i
    oveq1i
    @22
    @17
    @19
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
    @30
    @7
    caddc
    co
    @8
    @17
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    @19
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @22
    @32
    wceq
    @16
    cA
    @25
    @26
    mulcli
    #
    @26
    c9
    cB
    9cn
    @29
    mulcli
    #
    @29
    @33
    @34
    wa
    @35
    @36
    wa
    wa
    @21
    @31
    cC
    caddc
    @17
    cA
    @19
    cB
    add4
    oveq1d
    mp4an
    @30
    @6
    cC
    @17
    @19
    @37
    @38
    addcli
    cA
    cB
    @26
    @29
    addcli
    cC
    3dvds2dec.c
    nn0cni
    addassi
    @30
    @5
    @7
    caddc
    @30
    c9
    @2
    cmul
    co
    #
    @19
    caddc
    co
    #
    c9
    @3
    cmul
    co
    #
    @5
    @17
    @39
    @19
    caddc
    @17
    c9
    @1
    cmul
    co
    #
    cA
    cmul
    co
    @39
    @16
    @42
    cA
    cmul
    @42
    @16
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
    @26
    mulassi
    eqtri
    oveq1i
    @41
    @40
    c9
    @2
    cB
    9cn
    @1
    cA
    @44
    @26
    mulcli
    #
    @29
    adddii
    eqcomi
    @41
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
    @46
    @3
    cmul
    @46
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
    @45
    @29
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
    @48
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    @51
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
    @49
    @50
    @47
    @4
    cz
    wcel
    #
    @49
    3z
    @47
    @3
    cz
    wcel
    #
    @56
    3z
    @2
    cz
    wcel
    #
    @53
    @57
    @1
    cz
    wcel
    @52
    @58
    @1
    @43
    nn0zi
    @54
    @1
    cA
    zmulcl
    mp2an
    @55
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
    @47
    @56
    @50
    3z
    @59
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
