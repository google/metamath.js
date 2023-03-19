include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cc0.mm"
include "cmo.mm"
include "co.mm"
include "cmin.mm"
include "cfzo.mm"
include "caddc.mm"
include "wceq.mm"
include "cr.mm"
include "crp.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "elfzoelz.mm"
include "zred.mm"
include "adantr.mm"
include "zmodcl.mm"
include "nn0red.mm"
include "adantl.mm"
include "readdcld.mm"
include "ancoms.mm"
include "nnrp.mm"
include "ad2antlr.mm"
include "elfzole1.mm"
include "nn0ge0d.mm"
include "addge0d.mm"
include "elfzolt2.mm"
include "nnre.mm"
include "ltaddsubd.mm"
include "mpbird.mm"
include "modid.mm"
include "syl22anc.mm"
include "zre.mm"
include "modadd2mod.mm"
include "syl3anc.mm"
include "eqtr3d.mm"
include "ex.mm"

theorem modaddmodlo
  let cA: class A
  let cB: class B
  let cM: class M


  assert |- ( ( A e. ZZ /\ M e. NN ) -> ( B e. ( 0 ..^ ( M - ( A mod M ) ) ) -> ( B + ( A mod M ) ) = ( ( B + A ) mod M ) ) )

  proof
    cA
    cz
    wcel
    #
    cM
    cn
    wcel
    #
    wa
    #
    cB
    cc0
    cM
    cA
    cM
    cmo
    co
    #
    cmin
    co
    #
    cfzo
    co
    wcel
    #
    cB
    @3
    caddc
    co
    #
    cB
    cA
    caddc
    co
    cM
    cmo
    co
    #
    wceq
    @2
    @5
    wa
    #
    @6
    cM
    cmo
    co
    #
    @6
    @7
    @8
    @6
    cr
    wcel
    #
    cM
    crp
    wcel
    #
    cc0
    @6
    cle
    wbr
    @6
    cM
    clt
    wbr
    #
    @9
    @6
    wceq
    @5
    @2
    @10
    @5
    @2
    wa
    cB
    @3
    @5
    cB
    cr
    wcel
    #
    @2
    @5
    cB
    cB
    cc0
    @4
    elfzoelz
    zred
    #
    adantr
    @2
    @3
    cr
    wcel
    #
    @5
    @2
    @3
    cA
    cM
    zmodcl
    #
    nn0red
    #
    adantl
    readdcld
    ancoms
    @1
    @11
    @0
    @5
    cM
    nnrp
    ad2antlr
    #
    @8
    cB
    @3
    @5
    @13
    @2
    @14
    adantl
    #
    @2
    @15
    @5
    @17
    adantr
    #
    @5
    cc0
    cB
    cle
    wbr
    @2
    cB
    cc0
    @4
    elfzole1
    adantl
    @2
    cc0
    @3
    cle
    wbr
    @5
    @2
    @3
    @16
    nn0ge0d
    adantr
    addge0d
    @8
    @12
    cB
    @4
    clt
    wbr
    #
    @5
    @21
    @2
    cB
    cc0
    @4
    elfzolt2
    adantl
    @8
    cB
    @3
    cM
    @19
    @20
    @1
    cM
    cr
    wcel
    @0
    @5
    cM
    nnre
    ad2antlr
    ltaddsubd
    mpbird
    @6
    cM
    modid
    syl22anc
    @8
    cA
    cr
    wcel
    #
    @13
    @11
    @9
    @7
    wceq
    @2
    @22
    @5
    @0
    @22
    @1
    cA
    zre
    adantr
    adantr
    @19
    @18
    cA
    cB
    cM
    modadd2mod
    syl3anc
    eqtr3d
    ex
end
