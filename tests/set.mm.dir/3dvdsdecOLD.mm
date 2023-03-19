include "c3.mm"
include "cdc.mm"
include "cdvds.mm"
include "wbr.mm"
include "c9.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "c10.mm"
include "dfdecOLD.mm"
include "c1.mm"
include "df-10OLD.mm"
include "oveq1i.mm"
include "9cn.mm"
include "ax-1cn.mm"
include "nn0cni.mm"
include "adddiri.mm"
include "mulid2i.mm"
include "oveq2i.mm"
include "3eqtri.mm"
include "mulcli.mm"
include "addassi.mm"
include "breq2i.mm"
include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "3z.mm"
include "nn0zi.mm"
include "zaddcl.mm"
include "mp2an.mm"
include "9nn.mm"
include "nnzi.mm"
include "zmulcl.mm"
include "dvdsmul1.mm"
include "3t3e9.mm"
include "eqcomi.mm"
include "3cn.mm"
include "mulassi.mm"
include "eqtri.mm"
include "breqtrri.mm"
include "pm3.2i.mm"
include "dvdsadd2b.mm"
include "mp3an.mm"
include "bitr4i.mm"

theorem 3dvdsdecOLD
  let cA: class A
  let cB: class B
  assume 3dvdsdec.a: |- A e. NN0
  assume 3dvdsdec.b: |- B e. NN0


  assert |- ( 3 || ; A B <-> 3 || ( A + B ) )

  proof
    c3
    cA
    cB
    cdc
    #
    cdvds
    wbr
    c3
    c9
    cA
    cmul
    co
    #
    cA
    cB
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
    @2
    cdvds
    wbr
    #
    @0
    @3
    c3
    cdvds
    @0
    c10
    cA
    cmul
    co
    #
    cB
    caddc
    co
    @1
    cA
    caddc
    co
    #
    cB
    caddc
    co
    @3
    cA
    cB
    dfdecOLD
    @6
    @7
    cB
    caddc
    @6
    c9
    c1
    caddc
    co
    #
    cA
    cmul
    co
    @1
    c1
    cA
    cmul
    co
    #
    caddc
    co
    @7
    c10
    @8
    cA
    cmul
    df-10OLD
    oveq1i
    c9
    c1
    cA
    9cn
    ax-1cn
    cA
    3dvdsdec.a
    nn0cni
    #
    adddiri
    @9
    cA
    @1
    caddc
    cA
    @10
    mulid2i
    oveq2i
    3eqtri
    oveq1i
    @1
    cA
    cB
    c9
    cA
    9cn
    @10
    mulcli
    @10
    cB
    3dvdsdec.b
    nn0cni
    addassi
    3eqtri
    breq2i
    c3
    cz
    wcel
    #
    @2
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    c3
    @1
    cdvds
    wbr
    #
    wa
    @5
    @4
    wb
    3z
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    @12
    cA
    3dvdsdec.a
    nn0zi
    #
    cB
    3dvdsdec.b
    nn0zi
    cA
    cB
    zaddcl
    mp2an
    @13
    @14
    c9
    cz
    wcel
    @15
    @13
    c9
    9nn
    nnzi
    @16
    c9
    cA
    zmulcl
    mp2an
    c3
    c3
    c3
    cA
    cmul
    co
    #
    cmul
    co
    #
    @1
    cdvds
    @11
    @17
    cz
    wcel
    #
    c3
    @18
    cdvds
    wbr
    3z
    @11
    @15
    @19
    3z
    @16
    c3
    cA
    zmulcl
    mp2an
    c3
    @17
    dvdsmul1
    mp2an
    @1
    c3
    c3
    cmul
    co
    #
    cA
    cmul
    co
    @18
    c9
    @20
    cA
    cmul
    @20
    c9
    3t3e9
    eqcomi
    oveq1i
    c3
    c3
    cA
    3cn
    3cn
    @10
    mulassi
    eqtri
    breqtrri
    pm3.2i
    c3
    @2
    @1
    dvdsadd2b
    mp3an
    bitr4i
end
