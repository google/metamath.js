include "clt.mm"
include "wbr.mm"
include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "w3a.mm"
include "cmo.mm"
include "cmin.mm"
include "cif.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "cr.mm"
include "crp.mm"
include "cc0.mm"
include "cle.mm"
include "nn0re.mm"
include "nnrp.mm"
include "anim12i.mm"
include "3adant3.mm"
include "adantl.mm"
include "nn0ge0.mm"
include "3ad2ant1.mm"
include "anim1i.mm"
include "ancoms.mm"
include "modid.mm"
include "syl2anc.mm"
include "iftrue.mm"
include "eqcomd.mm"
include "adantr.mm"
include "eqtrd.mm"
include "ex.mm"
include "wn.mm"
include "wb.mm"
include "nnre.mm"
include "lenlt.mm"
include "syl2anr.mm"
include "biimpar.mm"
include "simpl3.mm"
include "2submod.mm"
include "syl12anc.mm"
include "iffalse.mm"
include "expcom.mm"
include "pm2.61i.mm"

theorem modifeq2int
  let cA: class A
  let cB: class B


  assert |- ( ( A e. NN0 /\ B e. NN /\ A < ( 2 x. B ) ) -> ( A mod B ) = if ( A < B , A , ( A - B ) ) )

  proof
    cA
    cB
    clt
    wbr
    #
    cA
    cn0
    wcel
    #
    cB
    cn
    wcel
    #
    cA
    c2
    cB
    cmul
    co
    clt
    wbr
    #
    w3a
    #
    cA
    cB
    cmo
    co
    #
    @0
    cA
    cA
    cB
    cmin
    co
    #
    cif
    #
    wceq
    #
    wi
    @0
    @4
    @8
    @0
    @4
    wa
    #
    @5
    cA
    @7
    @9
    cA
    cr
    wcel
    #
    cB
    crp
    wcel
    #
    wa
    #
    cc0
    cA
    cle
    wbr
    #
    @0
    wa
    #
    @5
    cA
    wceq
    @4
    @12
    @0
    @1
    @2
    @12
    @3
    @1
    @10
    @2
    @11
    cA
    nn0re
    #
    cB
    nnrp
    anim12i
    3adant3
    #
    adantl
    @4
    @0
    @14
    @4
    @13
    @0
    @1
    @2
    @13
    @3
    cA
    nn0ge0
    3ad2ant1
    anim1i
    ancoms
    cA
    cB
    modid
    syl2anc
    @0
    cA
    @7
    wceq
    @4
    @0
    @7
    cA
    @0
    cA
    @6
    iftrue
    eqcomd
    adantr
    eqtrd
    ex
    @4
    @0
    wn
    #
    @8
    @4
    @17
    wa
    #
    @5
    @6
    @7
    @18
    @12
    cB
    cA
    cle
    wbr
    #
    @3
    @5
    @6
    wceq
    @4
    @12
    @17
    @16
    adantr
    @4
    @19
    @17
    @1
    @2
    @19
    @17
    wb
    #
    @3
    @2
    cB
    cr
    wcel
    @10
    @20
    @1
    cB
    nnre
    @15
    cB
    cA
    lenlt
    syl2anr
    3adant3
    biimpar
    @1
    @2
    @3
    @17
    simpl3
    cA
    cB
    2submod
    syl12anc
    @18
    @7
    @6
    @17
    @7
    @6
    wceq
    @4
    @0
    cA
    @6
    iffalse
    adantl
    eqcomd
    eqtrd
    expcom
    pm2.61i
end
