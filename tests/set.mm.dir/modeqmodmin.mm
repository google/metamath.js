include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cmo.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "modid0.mm"
include "adantl.mm"
include "modge0.mm"
include "eqbrtrd.mm"
include "wb.mm"
include "simpl.mm"
include "rpre.mm"
include "simpr.mm"
include "modsubdir.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "modcl.mm"
include "recnd.mm"
include "subid1d.mm"
include "3eqtr2rd.mm"

theorem modeqmodmin
  let cA: class A
  let cM: class M


  assert |- ( ( A e. RR /\ M e. RR+ ) -> ( A mod M ) = ( ( A - M ) mod M ) )

  proof
    cA
    cr
    wcel
    #
    cM
    crp
    wcel
    #
    wa
    #
    cA
    cM
    cmin
    co
    cM
    cmo
    co
    #
    cA
    cM
    cmo
    co
    #
    cM
    cM
    cmo
    co
    #
    cmin
    co
    #
    @4
    cc0
    cmin
    co
    @4
    @2
    @5
    @4
    cle
    wbr
    #
    @3
    @6
    wceq
    #
    @2
    @5
    cc0
    @4
    cle
    @1
    @5
    cc0
    wceq
    @0
    cM
    modid0
    adantl
    #
    cA
    cM
    modge0
    eqbrtrd
    @2
    @0
    cM
    cr
    wcel
    #
    @1
    @7
    @8
    wb
    @0
    @1
    simpl
    @1
    @10
    @0
    cM
    rpre
    adantl
    @0
    @1
    simpr
    cA
    cM
    cM
    modsubdir
    syl3anc
    mpbid
    @2
    cc0
    @5
    @4
    cmin
    @2
    @5
    cc0
    @9
    eqcomd
    oveq2d
    @2
    @4
    @2
    @4
    cA
    cM
    modcl
    recnd
    subid1d
    3eqtr2rd
end
