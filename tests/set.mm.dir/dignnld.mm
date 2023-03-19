include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cn.mm"
include "clogb.mm"
include "co.mm"
include "cfl.mm"
include "c1.mm"
include "caddc.mm"
include "w3a.mm"
include "cdig.mm"
include "cexp.mm"
include "cdiv.mm"
include "cmo.mm"
include "cc0.mm"
include "cn0.mm"
include "cpnf.mm"
include "cico.mm"
include "wceq.mm"
include "eluz2nn.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "crp.mm"
include "nnrp.mm"
include "anim2i.mm"
include "relogbzcl.mm"
include "syl.mm"
include "nnre.mm"
include "nnge1.mm"
include "jca.mm"
include "wb.mm"
include "1re.mm"
include "elicopnf.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "rege1logbzge0.mm"
include "flge0nn0.mm"
include "peano2nn0.mm"
include "3syl.mm"
include "eluznn0.mm"
include "stoic3.mm"
include "nnnn0.mm"
include "nn0rp0.mm"
include "3ad2ant2.mm"
include "nn0digval.mm"
include "syl3anc.mm"
include "clt.mm"
include "eluzelre.mm"
include "wne.mm"
include "eluz2n0.mm"
include "cz.mm"
include "eluzelz.mm"
include "3ad2ant3.mm"
include "reexpclzd.mm"
include "cc.mm"
include "eluzelcn.mm"
include "expne0d.mm"
include "redivcld.mm"
include "nn0ge0.mm"
include "nngt0d.mm"
include "expgt0.mm"
include "ge0div.mm"
include "mpbid.mm"
include "dignn0ldlem.mm"
include "nnrpd.mm"
include "rpexpcl.mm"
include "syl2an.mm"
include "3adant2.mm"
include "divlt1lt.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "cxr.mm"
include "0re.mm"
include "rexri.mm"
include "pm3.2i.mm"
include "elico2.mm"
include "mp1i.mm"
include "mpbir3and.mm"
include "ico01fl0.mm"
include "oveq1d.mm"
include "0mod.mm"
include "3eqtrd.mm"

theorem dignnld
  let cB: class B
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( B e. ( ZZ>= ` 2 ) /\ N e. NN /\ K e. ( ZZ>= ` ( ( |_ ` ( B logb N ) ) + 1 ) ) ) -> ( K ( digit ` B ) N ) = 0 )

  proof
    cB
    c2
    cuz
    cfv
    wcel
    #
    cN
    cn
    wcel
    #
    cK
    cB
    cN
    clogb
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cuz
    cfv
    wcel
    #
    w3a
    #
    cK
    cN
    cB
    cdig
    cfv
    co
    #
    cN
    cB
    cK
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    cB
    cmo
    co
    #
    cc0
    cB
    cmo
    co
    #
    cc0
    @6
    cB
    cn
    wcel
    #
    cK
    cn0
    wcel
    #
    cN
    cc0
    cpnf
    cico
    co
    wcel
    #
    @7
    @11
    wceq
    @0
    @1
    @13
    @5
    cB
    eluz2nn
    #
    3ad2ant1
    @0
    @1
    @4
    cn0
    wcel
    #
    @5
    @14
    @0
    @1
    wa
    #
    @2
    cr
    wcel
    #
    cc0
    @2
    cle
    wbr
    #
    wa
    @3
    cn0
    wcel
    @17
    @18
    @19
    @20
    @18
    @0
    cN
    crp
    wcel
    #
    wa
    @19
    @1
    @21
    @0
    cN
    nnrp
    anim2i
    cB
    cN
    relogbzcl
    syl
    @18
    @0
    cN
    c1
    cpnf
    cico
    co
    wcel
    #
    wa
    @20
    @1
    @22
    @0
    @1
    cN
    cr
    wcel
    #
    c1
    cN
    cle
    wbr
    #
    wa
    #
    @22
    @1
    @23
    @24
    cN
    nnre
    #
    cN
    nnge1
    jca
    c1
    cr
    wcel
    @22
    @25
    wb
    1re
    c1
    cN
    elicopnf
    ax-mp
    sylibr
    anim2i
    cB
    cN
    rege1logbzge0
    syl
    jca
    @2
    flge0nn0
    @3
    peano2nn0
    3syl
    cK
    @4
    eluznn0
    stoic3
    @1
    @0
    @15
    @5
    @1
    cN
    cn0
    wcel
    #
    @15
    cN
    nnnn0
    #
    cN
    nn0rp0
    syl
    3ad2ant2
    cB
    cN
    cK
    nn0digval
    syl3anc
    @6
    @10
    cc0
    cB
    cmo
    @6
    @9
    cc0
    c1
    cico
    co
    wcel
    #
    @10
    cc0
    wceq
    @6
    @29
    @9
    cr
    wcel
    #
    cc0
    @9
    cle
    wbr
    #
    @9
    c1
    clt
    wbr
    #
    @6
    cN
    @8
    @1
    @0
    @23
    @5
    @26
    3ad2ant2
    #
    @6
    cB
    cK
    @0
    @1
    cB
    cr
    wcel
    #
    @5
    c2
    cB
    eluzelre
    3ad2ant1
    #
    @0
    @1
    cB
    cc0
    wne
    @5
    cB
    eluz2n0
    3ad2ant1
    #
    @5
    @0
    cK
    cz
    wcel
    #
    @1
    @4
    cK
    eluzelz
    #
    3ad2ant3
    #
    reexpclzd
    #
    @6
    cB
    cK
    @0
    @1
    cB
    cc
    wcel
    @5
    c2
    cB
    eluzelcn
    3ad2ant1
    @36
    @39
    expne0d
    redivcld
    @6
    cc0
    cN
    cle
    wbr
    #
    @31
    @1
    @0
    @41
    @5
    @1
    @27
    @41
    @28
    cN
    nn0ge0
    syl
    3ad2ant2
    @6
    @23
    @8
    cr
    wcel
    cc0
    @8
    clt
    wbr
    #
    @41
    @31
    wb
    @33
    @40
    @6
    @34
    @37
    cc0
    cB
    clt
    wbr
    #
    @42
    @35
    @39
    @0
    @1
    @43
    @5
    @0
    cB
    @16
    nngt0d
    3ad2ant1
    cB
    cK
    expgt0
    syl3anc
    cN
    @8
    ge0div
    syl3anc
    mpbid
    @6
    @32
    cN
    @8
    clt
    wbr
    #
    cB
    cK
    cN
    dignn0ldlem
    @6
    @23
    @8
    crp
    wcel
    #
    @32
    @44
    wb
    @33
    @0
    @5
    @45
    @1
    @0
    cB
    crp
    wcel
    #
    @37
    @45
    @5
    @0
    cB
    @16
    nnrpd
    #
    @38
    cB
    cK
    rpexpcl
    syl2an
    3adant2
    cN
    @8
    divlt1lt
    syl2anc
    mpbird
    cc0
    cr
    wcel
    #
    c1
    cxr
    wcel
    #
    wa
    @29
    @30
    @31
    @32
    w3a
    wb
    @6
    @48
    @49
    0re
    c1
    1re
    rexri
    pm3.2i
    cc0
    c1
    @9
    elico2
    mp1i
    mpbir3and
    @9
    ico01fl0
    syl
    oveq1d
    @6
    @46
    @12
    cc0
    wceq
    @0
    @1
    @46
    @5
    @47
    3ad2ant1
    cB
    0mod
    syl
    3eqtrd
end
