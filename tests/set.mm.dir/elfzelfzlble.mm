include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cmin.mm"
include "cle.mm"
include "wa.mm"
include "elfz2.mm"
include "3simpc.mm"
include "adantr.mm"
include "sylbi.mm"
include "anim2i.mm"
include "simpl.mm"
include "ancomd.mm"
include "zsubcl.mm"
include "syl.mm"
include "adantl.mm"
include "simprr.mm"
include "3jca.mm"
include "3adant3.mm"
include "cr.mm"
include "wi.mm"
include "elfzel2.mm"
include "zred.mm"
include "zre.mm"
include "elfzelz.mm"
include "simp1.mm"
include "readdcl.mm"
include "3adant1.mm"
include "ltle.mm"
include "syl2anc.mm"
include "lesubadd2.mm"
include "sylibrd.mm"
include "3impia.mm"
include "elfzle2.mm"
include "3ad2ant2.mm"
include "jca32.mm"
include "sylibr.mm"

theorem elfzelfzlble
  let cK: class K
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( M e. ZZ /\ K e. ( 0 ... N ) /\ N < ( M + K ) ) -> K e. ( ( N - M ) ... N ) )

  proof
    cM
    cz
    wcel
    #
    cK
    cc0
    cN
    cfz
    co
    wcel
    #
    cN
    cM
    cK
    caddc
    co
    #
    clt
    wbr
    #
    w3a
    #
    cN
    cM
    cmin
    co
    #
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    w3a
    #
    @5
    cK
    cle
    wbr
    #
    cK
    cN
    cle
    wbr
    #
    wa
    wa
    cK
    @5
    cN
    cfz
    co
    wcel
    @4
    @9
    @10
    @11
    @0
    @1
    @9
    @3
    @0
    @1
    wa
    #
    @0
    @7
    @8
    wa
    #
    wa
    #
    @9
    @1
    @13
    @0
    @1
    cc0
    cz
    wcel
    #
    @7
    @8
    w3a
    #
    cc0
    cK
    cle
    wbr
    @11
    wa
    #
    wa
    @13
    cK
    cc0
    cN
    elfz2
    @16
    @13
    @17
    @15
    @7
    @8
    3simpc
    adantr
    sylbi
    anim2i
    @14
    @6
    @7
    @8
    @14
    @7
    @0
    wa
    @6
    @14
    @0
    @7
    @13
    @7
    @0
    @7
    @8
    simpl
    #
    anim2i
    ancomd
    cN
    cM
    zsubcl
    syl
    @13
    @7
    @0
    @18
    adantl
    @0
    @7
    @8
    simprr
    3jca
    syl
    3adant3
    @0
    @1
    @3
    @10
    @12
    cN
    cr
    wcel
    #
    cM
    cr
    wcel
    #
    cK
    cr
    wcel
    #
    w3a
    #
    @3
    @10
    wi
    @12
    @19
    @20
    @21
    @1
    @19
    @0
    @1
    cN
    cK
    cc0
    cN
    elfzel2
    zred
    adantl
    @0
    @20
    @1
    cM
    zre
    adantr
    @1
    @21
    @0
    @1
    cK
    cK
    cc0
    cN
    elfzelz
    zred
    adantl
    3jca
    @22
    @3
    cN
    @2
    cle
    wbr
    #
    @10
    @22
    @19
    @2
    cr
    wcel
    #
    @3
    @23
    wi
    @19
    @20
    @21
    simp1
    @20
    @21
    @24
    @19
    cM
    cK
    readdcl
    3adant1
    cN
    @2
    ltle
    syl2anc
    cN
    cM
    cK
    lesubadd2
    sylibrd
    syl
    3impia
    @1
    @0
    @11
    @3
    cK
    cc0
    cN
    elfzle2
    3ad2ant2
    jca32
    cK
    @5
    cN
    elfz2
    sylibr
end
