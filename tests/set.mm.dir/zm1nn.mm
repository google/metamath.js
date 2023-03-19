include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "c1.mm"
include "clt.mm"
include "w3a.mm"
include "cn0.mm"
include "cz.mm"
include "wa.mm"
include "cn.mm"
include "wi.mm"
include "0red.mm"
include "simpl.mm"
include "zre.mm"
include "nn0re.mm"
include "resubcl.mm"
include "syl2anr.mm"
include "adantl.mm"
include "peano2rem.mm"
include "syl.mm"
include "lelttr.mm"
include "syl3anc.mm"
include "1red.mm"
include "posdifd.mm"
include "caddc.mm"
include "adantr.mm"
include "ltaddsubd.mm"
include "elnn0z.mm"
include "leadd2d.mm"
include "1re.mm"
include "0re.mm"
include "readdcli.mm"
include "a1i.mm"
include "readdcld.mm"
include "peano2zm.mm"
include "ltaddsub2d.mm"
include "biimpd.mm"
include "imp.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "ex.mm"
include "syld.mm"
include "expd.mm"
include "sylbid.mm"
include "impancom.mm"
include "sylbi.mm"
include "sylbird.mm"
include "com23.mm"
include "3impib.mm"
include "com12.mm"

theorem zm1nn
  let cJ: class J
  let cL: class L
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. NN0 /\ L e. ZZ ) -> ( ( J e. RR /\ 0 <_ J /\ J < ( ( L - N ) - 1 ) ) -> ( L - 1 ) e. NN ) )

  proof
    cJ
    cr
    wcel
    #
    cc0
    cJ
    cle
    wbr
    #
    cJ
    cL
    cN
    cmin
    co
    #
    c1
    cmin
    co
    #
    clt
    wbr
    #
    w3a
    cN
    cn0
    wcel
    #
    cL
    cz
    wcel
    #
    wa
    #
    cL
    c1
    cmin
    co
    #
    cn
    wcel
    #
    @0
    @1
    @4
    @7
    @9
    wi
    @0
    @7
    @1
    @4
    wa
    #
    @9
    @0
    @7
    @10
    @9
    wi
    @0
    @7
    wa
    #
    @10
    cc0
    @3
    clt
    wbr
    #
    @9
    @11
    cc0
    cr
    wcel
    @0
    @3
    cr
    wcel
    #
    @10
    @12
    wi
    @11
    0red
    @0
    @7
    simpl
    @11
    @2
    cr
    wcel
    #
    @13
    @7
    @14
    @0
    @6
    cL
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @14
    @5
    cL
    zre
    #
    cN
    nn0re
    #
    cL
    cN
    resubcl
    syl2anr
    #
    adantl
    @2
    peano2rem
    syl
    cc0
    cJ
    @3
    lelttr
    syl3anc
    @7
    @12
    @9
    wi
    @0
    @7
    @12
    c1
    @2
    clt
    wbr
    #
    @9
    @7
    c1
    @2
    @7
    1red
    #
    @19
    posdifd
    @7
    @20
    c1
    cN
    caddc
    co
    #
    cL
    clt
    wbr
    #
    @9
    @7
    c1
    cN
    cL
    @21
    @5
    @16
    @6
    @18
    adantr
    @6
    @15
    @5
    @17
    adantl
    ltaddsubd
    @5
    @6
    @23
    @9
    wi
    #
    @5
    cN
    cz
    wcel
    #
    cc0
    cN
    cle
    wbr
    #
    wa
    @6
    @24
    wi
    cN
    elnn0z
    @25
    @6
    @26
    @24
    @25
    @6
    wa
    #
    @26
    c1
    cc0
    caddc
    co
    #
    @22
    cle
    wbr
    #
    @24
    @27
    cc0
    cN
    c1
    @27
    0red
    @25
    @16
    @6
    cN
    zre
    #
    adantr
    @27
    1red
    leadd2d
    @27
    @29
    @23
    @9
    @27
    @29
    @23
    wa
    #
    @28
    cL
    clt
    wbr
    #
    @9
    @27
    @28
    cr
    wcel
    #
    @22
    cr
    wcel
    #
    @15
    @31
    @32
    wi
    @33
    @27
    c1
    cc0
    1re
    0re
    readdcli
    a1i
    @25
    @34
    @6
    @25
    c1
    cN
    @25
    1red
    @30
    readdcld
    adantr
    @6
    @15
    @25
    @17
    adantl
    @28
    @22
    cL
    lelttr
    syl3anc
    @27
    @32
    @9
    @27
    @32
    wa
    @8
    cz
    wcel
    #
    cc0
    @8
    clt
    wbr
    #
    @9
    @27
    @35
    @32
    @6
    @35
    @25
    cL
    peano2zm
    adantl
    adantr
    @27
    @32
    @36
    @6
    @32
    @36
    wi
    @25
    @6
    @32
    @36
    @6
    c1
    cc0
    cL
    @6
    1red
    @6
    0red
    @17
    ltaddsub2d
    biimpd
    adantl
    imp
    @8
    elnnz
    sylanbrc
    ex
    syld
    expd
    sylbid
    impancom
    sylbi
    imp
    sylbird
    sylbird
    adantl
    syld
    ex
    com23
    3impib
    com12
end
