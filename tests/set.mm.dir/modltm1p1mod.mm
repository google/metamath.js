include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "cmo.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "caddc.mm"
include "wceq.mm"
include "wa.mm"
include "simpl.mm"
include "1red.mm"
include "simpr.mm"
include "3jca.mm"
include "3adant3.mm"
include "modaddmod.mm"
include "syl.mm"
include "cc0.mm"
include "cle.mm"
include "modcl.mm"
include "peano2re.mm"
include "jca.mm"
include "0red.mm"
include "modge0.mm"
include "lep1d.mm"
include "letrd.mm"
include "rpre.mm"
include "adantl.mm"
include "ltaddsubd.mm"
include "biimp3ar.mm"
include "modid.mm"
include "syl12anc.mm"
include "eqtr3d.mm"

theorem modltm1p1mod
  let cA: class A
  let cM: class M


  assert |- ( ( A e. RR /\ M e. RR+ /\ ( A mod M ) < ( M - 1 ) ) -> ( ( A + 1 ) mod M ) = ( ( A mod M ) + 1 ) )

  proof
    cA
    cr
    wcel
    #
    cM
    crp
    wcel
    #
    cA
    cM
    cmo
    co
    #
    cM
    c1
    cmin
    co
    clt
    wbr
    #
    w3a
    #
    @2
    c1
    caddc
    co
    #
    cM
    cmo
    co
    #
    cA
    c1
    caddc
    co
    cM
    cmo
    co
    #
    @5
    @4
    @0
    c1
    cr
    wcel
    #
    @1
    w3a
    #
    @6
    @7
    wceq
    @0
    @1
    @9
    @3
    @0
    @1
    wa
    #
    @0
    @8
    @1
    @0
    @1
    simpl
    @10
    1red
    #
    @0
    @1
    simpr
    #
    3jca
    3adant3
    cA
    c1
    cM
    modaddmod
    syl
    @4
    @5
    cr
    wcel
    #
    @1
    wa
    #
    cc0
    @5
    cle
    wbr
    #
    @5
    cM
    clt
    wbr
    #
    @6
    @5
    wceq
    @0
    @1
    @14
    @3
    @10
    @13
    @1
    @10
    @2
    cr
    wcel
    @13
    cA
    cM
    modcl
    #
    @2
    peano2re
    syl
    #
    @12
    jca
    3adant3
    @0
    @1
    @15
    @3
    @10
    cc0
    @2
    @5
    @10
    0red
    @17
    @18
    cA
    cM
    modge0
    @10
    @2
    @17
    lep1d
    letrd
    3adant3
    @0
    @1
    @16
    @3
    @10
    @2
    c1
    cM
    @17
    @11
    @1
    cM
    cr
    wcel
    @0
    cM
    rpre
    adantl
    ltaddsubd
    biimp3ar
    @5
    cM
    modid
    syl12anc
    eqtr3d
end
