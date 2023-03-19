include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "cfz.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "wb.mm"
include "elfz1.mm"
include "3adant3.mm"
include "wi.mm"
include "wa.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "zre.mm"
include "nnre.mm"
include "nngt0.mm"
include "jca.mm"
include "lemul2.mm"
include "syl3an.mm"
include "3expa.mm"
include "biimpd.mm"
include "adantllr.mm"
include "ancom1s.mm"
include "adantlll.mm"
include "anim12d.mm"
include "zmulcl.mm"
include "ex.mm"
include "3anim123d.mm"
include "elfz.mm"
include "3coml.mm"
include "syl6.mm"
include "nnz.mm"
include "syl11.mm"
include "imp.mm"
include "sylibrd.mm"
include "an32s.mm"
include "exp4b.mm"
include "3impd.mm"
include "3impa.mm"
include "sylbid.mm"

theorem fzmul
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ /\ K e. NN ) -> ( J e. ( M ... N ) -> ( K x. J ) e. ( ( K x. M ) ... ( K x. N ) ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cK
    cn
    wcel
    #
    w3a
    cJ
    cM
    cN
    cfz
    co
    wcel
    #
    cJ
    cz
    wcel
    #
    cM
    cJ
    cle
    wbr
    #
    cJ
    cN
    cle
    wbr
    #
    w3a
    #
    cK
    cJ
    cmul
    co
    #
    cK
    cM
    cmul
    co
    #
    cK
    cN
    cmul
    co
    #
    cfz
    co
    wcel
    #
    @0
    @1
    @3
    @7
    wb
    @2
    cJ
    cM
    cN
    elfz1
    3adant3
    @0
    @1
    @2
    @7
    @11
    wi
    @0
    @1
    wa
    #
    @2
    wa
    #
    @4
    @5
    @6
    @11
    @13
    @4
    @5
    @6
    @11
    @12
    @4
    @2
    @5
    @6
    wa
    #
    @11
    wi
    @12
    @4
    wa
    #
    @2
    wa
    #
    @14
    @9
    @8
    cle
    wbr
    #
    @8
    @10
    cle
    wbr
    #
    wa
    #
    @11
    @16
    @5
    @17
    @6
    @18
    @0
    @4
    @2
    @5
    @17
    wi
    @1
    @0
    @4
    wa
    @2
    wa
    @5
    @17
    @0
    @4
    @2
    @5
    @17
    wb
    #
    @0
    cM
    cr
    wcel
    @4
    cJ
    cr
    wcel
    #
    @2
    cK
    cr
    wcel
    #
    cc0
    cK
    clt
    wbr
    #
    wa
    #
    @20
    cM
    zre
    cJ
    zre
    #
    @2
    @22
    @23
    cK
    nnre
    cK
    nngt0
    jca
    #
    cM
    cJ
    cK
    lemul2
    syl3an
    3expa
    biimpd
    adantllr
    @1
    @4
    @2
    @6
    @18
    wi
    @0
    @1
    @4
    wa
    @2
    wa
    @6
    @18
    @4
    @1
    @2
    @6
    @18
    wb
    #
    @4
    @1
    @2
    @27
    @4
    @21
    @1
    cN
    cr
    wcel
    @2
    @24
    @27
    @25
    cN
    zre
    @26
    cJ
    cN
    cK
    lemul2
    syl3an
    3expa
    ancom1s
    biimpd
    adantlll
    anim12d
    @15
    @2
    @11
    @19
    wb
    #
    @0
    @1
    @4
    @2
    @28
    wi
    cK
    cz
    wcel
    #
    @0
    @1
    @4
    w3a
    #
    @28
    @2
    @29
    @30
    @9
    cz
    wcel
    #
    @10
    cz
    wcel
    #
    @8
    cz
    wcel
    #
    w3a
    @28
    @29
    @0
    @31
    @1
    @32
    @4
    @33
    @29
    @0
    @31
    cK
    cM
    zmulcl
    ex
    @29
    @1
    @32
    cK
    cN
    zmulcl
    ex
    @29
    @4
    @33
    cK
    cJ
    zmulcl
    ex
    3anim123d
    @33
    @31
    @32
    @28
    @8
    @9
    @10
    elfz
    3coml
    syl6
    cK
    nnz
    syl11
    3expa
    imp
    sylibrd
    an32s
    exp4b
    3impd
    3impa
    sylbid
end
