include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "cn0.mm"
include "cdif.mm"
include "w3a.mm"
include "cdig.mm"
include "cfv.mm"
include "co.mm"
include "cneg.mm"
include "cexp.mm"
include "cmul.mm"
include "cfl.mm"
include "cmo.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "wceq.mm"
include "id.mm"
include "eldifi.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "digval.mm"
include "syl3an.mm"
include "nnz.mm"
include "wn.mm"
include "wa.mm"
include "eldif.mm"
include "znnn0nn.mm"
include "sylbi.mm"
include "nnnn0d.mm"
include "zexpcl.mm"
include "syl2an.mm"
include "3adant3.mm"
include "nn0z.mm"
include "3ad2ant3.mm"
include "zmulcld.mm"
include "flid.mm"
include "syl.mm"
include "oveq1d.mm"
include "cdiv.mm"
include "c1.mm"
include "cmin.mm"
include "cc.mm"
include "wne.mm"
include "nnre.mm"
include "reexpcl.mm"
include "recnd.mm"
include "nn0cn.mm"
include "nncn.mm"
include "nnne0.mm"
include "jca.mm"
include "3ad2ant1.mm"
include "div23.mm"
include "syl3anc.mm"
include "nnzd.mm"
include "3ad2ant2.mm"
include "expm1d.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "nnm1nn0.mm"
include "eqeltrd.mm"
include "crp.mm"
include "wb.mm"
include "remulcld.mm"
include "nnrp.mm"
include "mod0.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem dignn0fr
  let cB: class B
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( B e. NN /\ K e. ( ZZ \ NN0 ) /\ N e. NN0 ) -> ( K ( digit ` B ) N ) = 0 )

  proof
    cB
    cn
    wcel
    #
    cK
    cz
    cn0
    cdif
    wcel
    #
    cN
    cn0
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
    cB
    cK
    cneg
    #
    cexp
    co
    #
    cN
    cmul
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
    @0
    @0
    @1
    cK
    cz
    wcel
    #
    @2
    cN
    cc0
    cpnf
    cico
    co
    wcel
    #
    @4
    @9
    wceq
    @0
    id
    cK
    cz
    cn0
    eldifi
    @2
    cN
    cr
    wcel
    #
    cc0
    cN
    cle
    wbr
    @11
    cN
    nn0re
    #
    cN
    nn0ge0
    cN
    elrege0
    sylanbrc
    cB
    cN
    cK
    digval
    syl3an
    @3
    @9
    @7
    cB
    cmo
    co
    #
    cc0
    @3
    @8
    @7
    cB
    cmo
    @3
    @7
    cz
    wcel
    @8
    @7
    wceq
    @3
    @6
    cN
    @0
    @1
    @6
    cz
    wcel
    #
    @2
    @0
    cB
    cz
    wcel
    #
    @5
    cn0
    wcel
    #
    @15
    @1
    cB
    nnz
    #
    @1
    @5
    @1
    @10
    cK
    cn0
    wcel
    wn
    wa
    @5
    cn
    wcel
    #
    cK
    cz
    cn0
    eldif
    cK
    znnn0nn
    sylbi
    #
    nnnn0d
    #
    cB
    @5
    zexpcl
    syl2an
    3adant3
    @2
    @0
    cN
    cz
    wcel
    @1
    cN
    nn0z
    3ad2ant3
    #
    zmulcld
    @7
    flid
    syl
    oveq1d
    @3
    @14
    cc0
    wceq
    #
    @7
    cB
    cdiv
    co
    #
    cz
    wcel
    #
    @3
    @24
    cB
    @5
    c1
    cmin
    co
    #
    cexp
    co
    #
    cN
    cmul
    co
    #
    cz
    @3
    @24
    @6
    cB
    cdiv
    co
    #
    cN
    cmul
    co
    #
    @28
    @3
    @6
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    #
    @24
    @30
    wceq
    @0
    @1
    @31
    @2
    @0
    @1
    wa
    @6
    @0
    cB
    cr
    wcel
    @17
    @6
    cr
    wcel
    #
    @1
    cB
    nnre
    @21
    cB
    @5
    reexpcl
    syl2an
    #
    recnd
    3adant3
    @2
    @0
    @32
    @1
    cN
    nn0cn
    3ad2ant3
    @0
    @1
    @35
    @2
    @0
    @33
    @34
    cB
    nncn
    #
    cB
    nnne0
    #
    jca
    3ad2ant1
    @6
    cN
    cB
    div23
    syl3anc
    @3
    @29
    @27
    cN
    cmul
    @3
    @27
    @29
    @3
    cB
    @5
    @0
    @1
    @33
    @2
    @38
    3ad2ant1
    @0
    @1
    @34
    @2
    @39
    3ad2ant1
    @1
    @0
    @5
    cz
    wcel
    @2
    @1
    @5
    @20
    nnzd
    3ad2ant2
    expm1d
    eqcomd
    oveq1d
    eqtrd
    @3
    @27
    cN
    @0
    @1
    @27
    cz
    wcel
    #
    @2
    @0
    @16
    @26
    cn0
    wcel
    #
    @40
    @1
    @18
    @1
    @19
    @41
    @20
    @5
    nnm1nn0
    syl
    cB
    @26
    zexpcl
    syl2an
    3adant3
    @22
    zmulcld
    eqeltrd
    @3
    @7
    cr
    wcel
    cB
    crp
    wcel
    #
    @23
    @25
    wb
    @3
    @6
    cN
    @0
    @1
    @36
    @2
    @37
    3adant3
    @2
    @0
    @12
    @1
    @13
    3ad2ant3
    remulcld
    @0
    @1
    @42
    @2
    cB
    nnrp
    3ad2ant1
    @7
    cB
    mod0
    syl2anc
    mpbird
    eqtrd
    eqtrd
end
