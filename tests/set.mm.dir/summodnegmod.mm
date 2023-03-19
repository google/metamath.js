include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "cmo.mm"
include "co.mm"
include "cneg.mm"
include "wceq.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "caddc.mm"
include "cc0.mm"
include "wb.mm"
include "simp3.mm"
include "simp1.mm"
include "znegcl.mm"
include "3ad2ant2.mm"
include "moddvds.mm"
include "syl3anc.mm"
include "cc.mm"
include "wa.mm"
include "zcn.mm"
include "anim12i.mm"
include "3adant3.mm"
include "subneg.mm"
include "eqcomd.mm"
include "syl.mm"
include "breq2d.mm"
include "zaddcl.mm"
include "dvdsval3.mm"
include "syl2anc.mm"
include "3bitr2rd.mm"

theorem summodnegmod
  let cA: class A
  let cB: class B
  let cN: class N


  assert |- ( ( A e. ZZ /\ B e. ZZ /\ N e. NN ) -> ( ( ( A + B ) mod N ) = 0 <-> ( A mod N ) = ( -u B mod N ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cN
    cn
    wcel
    #
    w3a
    #
    cA
    cN
    cmo
    co
    cB
    cneg
    #
    cN
    cmo
    co
    wceq
    #
    cN
    cA
    @4
    cmin
    co
    #
    cdvds
    wbr
    #
    cN
    cA
    cB
    caddc
    co
    #
    cdvds
    wbr
    #
    @8
    cN
    cmo
    co
    cc0
    wceq
    #
    @3
    @2
    @0
    @4
    cz
    wcel
    #
    @5
    @7
    wb
    @0
    @1
    @2
    simp3
    #
    @0
    @1
    @2
    simp1
    @1
    @0
    @11
    @2
    cB
    znegcl
    3ad2ant2
    cA
    @4
    cN
    moddvds
    syl3anc
    @3
    @8
    @6
    cN
    cdvds
    @3
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    @8
    @6
    wceq
    @0
    @1
    @15
    @2
    @0
    @13
    @1
    @14
    cA
    zcn
    cB
    zcn
    anim12i
    3adant3
    @15
    @6
    @8
    cA
    cB
    subneg
    eqcomd
    syl
    breq2d
    @3
    @2
    @8
    cz
    wcel
    #
    @9
    @10
    wb
    @12
    @0
    @1
    @16
    @2
    cA
    cB
    zaddcl
    3adant3
    cN
    @8
    dvdsval3
    syl2anc
    3bitr2rd
end
