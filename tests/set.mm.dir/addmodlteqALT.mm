include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "caddc.mm"
include "cmo.mm"
include "wceq.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "wb.mm"
include "cn0.mm"
include "clt.mm"
include "wi.mm"
include "elfzo0.mm"
include "wa.mm"
include "elfzoelz.mm"
include "simplrr.mm"
include "nn0z.mm"
include "ad2antrl.mm"
include "zaddcl.mm"
include "sylan.mm"
include "adantlr.mm"
include "3jca.mm"
include "exp31.mm"
include "syl.mm"
include "com12.mm"
include "3adant3.mm"
include "sylbi.mm"
include "3imp.mm"
include "moddvds.mm"
include "elfzoel2.mm"
include "zcn.mm"
include "subid1d.mm"
include "eqcomd.mm"
include "3ad2ant1.mm"
include "cc.mm"
include "zcnd.mm"
include "pnpcan2.mm"
include "syl3an.mm"
include "breq12d.mm"
include "fzocongeq.mm"
include "3bitrd.mm"

theorem addmodlteqALT
  let cS: class S
  let cI: class I
  let cJ: class J
  let cN: class N


  assert |- ( ( I e. ( 0 ..^ N ) /\ J e. ( 0 ..^ N ) /\ S e. ZZ ) -> ( ( ( I + S ) mod N ) = ( ( J + S ) mod N ) <-> I = J ) )

  proof
    cI
    cc0
    cN
    cfzo
    co
    #
    wcel
    #
    cJ
    @0
    wcel
    #
    cS
    cz
    wcel
    #
    w3a
    #
    cI
    cS
    caddc
    co
    #
    cN
    cmo
    co
    cJ
    cS
    caddc
    co
    #
    cN
    cmo
    co
    wceq
    #
    cN
    @5
    @6
    cmin
    co
    #
    cdvds
    wbr
    #
    cN
    cc0
    cmin
    co
    #
    cI
    cJ
    cmin
    co
    #
    cdvds
    wbr
    #
    cI
    cJ
    wceq
    #
    @4
    cN
    cn
    wcel
    #
    @5
    cz
    wcel
    #
    @6
    cz
    wcel
    #
    w3a
    #
    @7
    @9
    wb
    @1
    @2
    @3
    @17
    @1
    cI
    cn0
    wcel
    #
    @14
    cI
    cN
    clt
    wbr
    #
    w3a
    @2
    @3
    @17
    wi
    #
    wi
    #
    cI
    cN
    elfzo0
    @18
    @14
    @21
    @19
    @2
    @18
    @14
    wa
    #
    @20
    @2
    cJ
    cz
    wcel
    #
    @22
    @20
    wi
    cJ
    cc0
    cN
    elfzoelz
    #
    @23
    @22
    @3
    @17
    @23
    @22
    wa
    #
    @3
    wa
    @14
    @15
    @16
    @23
    @18
    @14
    @3
    simplrr
    @25
    cI
    cz
    wcel
    #
    @3
    @15
    @18
    @26
    @23
    @14
    cI
    nn0z
    ad2antrl
    cI
    cS
    zaddcl
    sylan
    @23
    @3
    @16
    @22
    cJ
    cS
    zaddcl
    adantlr
    3jca
    exp31
    syl
    com12
    3adant3
    sylbi
    3imp
    @5
    @6
    cN
    moddvds
    syl
    @4
    cN
    @10
    @8
    @11
    cdvds
    @1
    @2
    cN
    @10
    wceq
    #
    @3
    @1
    cN
    cz
    wcel
    #
    @27
    cI
    cc0
    cN
    elfzoel2
    @28
    @10
    cN
    @28
    cN
    cN
    zcn
    subid1d
    eqcomd
    syl
    3ad2ant1
    @1
    cI
    cc
    wcel
    @2
    cJ
    cc
    wcel
    @3
    cS
    cc
    wcel
    @8
    @11
    wceq
    @1
    cI
    cI
    cc0
    cN
    elfzoelz
    zcnd
    @2
    cJ
    @24
    zcnd
    cS
    zcn
    cI
    cJ
    cS
    pnpcan2
    syl3an
    breq12d
    @1
    @2
    @12
    @13
    wb
    @3
    cI
    cJ
    cc0
    cN
    fzocongeq
    3adant3
    3bitrd
end
