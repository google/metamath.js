include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cn0.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cmin.mm"
include "c1.mm"
include "elfzo0.mm"
include "cz.mm"
include "cle.mm"
include "wa.mm"
include "nnz.mm"
include "adantr.mm"
include "nn0z.mm"
include "adantl.mm"
include "zsubcld.mm"
include "ancoms.mm"
include "peano2zm.mm"
include "syl.mm"
include "3adant3.mm"
include "simp3.mm"
include "wb.mm"
include "anim12i.mm"
include "znnsub.mm"
include "mpbid.mm"
include "nnm1ge0.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "simp2.mm"
include "caddc.mm"
include "cc.mm"
include "nncn.mm"
include "nn0cn.mm"
include "1cnd.mm"
include "subsub4d.mm"
include "nn0p1gt0.mm"
include "cr.mm"
include "nn0re.mm"
include "peano2re.mm"
include "nnre.mm"
include "ltsubpos.mm"
include "syl2an.mm"
include "eqbrtrd.mm"
include "syl3anbrc.mm"
include "sylbi.mm"

theorem ubmelm1fzo
  let cK: class K
  let cN: class N


  assert |- ( K e. ( 0 ..^ N ) -> ( ( N - K ) - 1 ) e. ( 0 ..^ N ) )

  proof
    cK
    cc0
    cN
    cfzo
    co
    #
    wcel
    cK
    cn0
    wcel
    #
    cN
    cn
    wcel
    #
    cK
    cN
    clt
    wbr
    #
    w3a
    #
    cN
    cK
    cmin
    co
    #
    c1
    cmin
    co
    #
    @0
    wcel
    #
    cK
    cN
    elfzo0
    @4
    @6
    cn0
    wcel
    #
    @2
    @6
    cN
    clt
    wbr
    #
    @7
    @4
    @6
    cz
    wcel
    #
    cc0
    @6
    cle
    wbr
    #
    @8
    @1
    @2
    @10
    @3
    @1
    @2
    wa
    #
    @5
    cz
    wcel
    #
    @10
    @2
    @1
    @13
    @2
    @1
    wa
    cN
    cK
    @2
    cN
    cz
    wcel
    #
    @1
    cN
    nnz
    #
    adantr
    @1
    cK
    cz
    wcel
    #
    @2
    cK
    nn0z
    #
    adantl
    zsubcld
    ancoms
    @5
    peano2zm
    syl
    3adant3
    @4
    @5
    cn
    wcel
    #
    @11
    @4
    @3
    @18
    @1
    @2
    @3
    simp3
    @4
    @16
    @14
    wa
    #
    @3
    @18
    wb
    @1
    @2
    @19
    @3
    @1
    @16
    @2
    @14
    @17
    @15
    anim12i
    3adant3
    cK
    cN
    znnsub
    syl
    mpbid
    @5
    nnm1ge0
    syl
    @6
    elnn0z
    sylanbrc
    @1
    @2
    @3
    simp2
    @1
    @2
    @9
    @3
    @12
    @6
    cN
    cK
    c1
    caddc
    co
    #
    cmin
    co
    #
    cN
    clt
    @12
    cN
    cK
    c1
    @2
    cN
    cc
    wcel
    @1
    cN
    nncn
    adantl
    @1
    cK
    cc
    wcel
    @2
    cK
    nn0cn
    adantr
    @12
    1cnd
    subsub4d
    @12
    cc0
    @20
    clt
    wbr
    #
    @21
    cN
    clt
    wbr
    #
    @1
    @22
    @2
    cK
    nn0p1gt0
    adantr
    @1
    @20
    cr
    wcel
    #
    cN
    cr
    wcel
    @22
    @23
    wb
    @2
    @1
    cK
    cr
    wcel
    @24
    cK
    nn0re
    cK
    peano2re
    syl
    cN
    nnre
    @20
    cN
    ltsubpos
    syl2an
    mpbid
    eqbrtrd
    3adant3
    @6
    cN
    elfzo0
    syl3anbrc
    sylbi
end
