include "c8.mm"
include "cdc.mm"
include "c1.mm"
include "cc0.mm"
include "c2.mm"
include "c9.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cn.mm"
include "wcel.mm"
include "c3.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "c7.mm"
include "wa.mm"
include "cgbo.mm"
include "wi.mm"
include "codd.mm"
include "wral.mm"
include "wrex.mm"
include "8nn0.mm"
include "8nn.mm"
include "decnncl.mm"
include "cn0.mm"
include "10nn.mm"
include "2nn0.mm"
include "9nn0.mm"
include "deccl.mm"
include "nnexpcl.mm"
include "mp2an.mm"
include "nnmulcli.mm"
include "id.mm"
include "wceq.mm"
include "wb.mm"
include "breq2.mm"
include "anbi2d.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "adantl.mm"
include "simplr.mm"
include "simprl.mm"
include "simprr.mm"
include "tgblthelfgott.mm"
include "syl3anc.mm"
include "ex.mm"
include "ralrimiva.mm"
include "caddc.mm"
include "nngt0i.mm"
include "nnrei.mm"
include "3nn0.mm"
include "0nn0.mm"
include "ltaddposi.mm"
include "mpbi.mm"
include "dfdec10.mm"
include "oveq1i.mm"
include "nncni.mm"
include "8cn.mm"
include "adddiri.mm"
include "mulcomi.mm"
include "mulassi.mm"
include "nncn.mm"
include "a1i.mm"
include "expp1d.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "3eqtr2i.mm"
include "2p1e3.mm"
include "eqid.mm"
include "decsucc.mm"
include "oveq2i.mm"
include "cc.mm"
include "mulcom.mm"
include "oveq1d.mm"
include "3eqtri.mm"
include "breqtrri.mm"
include "jctil.mm"
include "rspcedvd.mm"

theorem tgoldbachlt
  let vm: setvar m
  let vn: setvar n
  let cN: class N
  let vd: setvar d
  let vf: setvar f
  let vi: setvar i
  let vk: setvar k
  let vx: setvar x

  disjoint m n
  disjoint N d
  disjoint N f
  disjoint N i
  disjoint N n
  disjoint d f
  disjoint d i
  disjoint d n
  disjoint f i
  disjoint f n
  disjoint i n
  disjoint k x
  assert |- E. m e. NN ( ( 8 x. ( ; 1 0 ^ ; 3 0 ) ) < m /\ A. n e. Odd ( ( 7 < n /\ n < m ) -> n e. GoldbachOdd ) )

  proof
    c8
    c8
    cdc
    #
    c1
    cc0
    cdc
    #
    c2
    c9
    cdc
    #
    cexp
    co
    #
    cmul
    co
    #
    cn
    wcel
    #
    c8
    @1
    c3
    cc0
    cdc
    #
    cexp
    co
    #
    cmul
    co
    #
    vm
    cv
    #
    clt
    wbr
    #
    c7
    vn
    cv
    #
    clt
    wbr
    #
    @11
    @9
    clt
    wbr
    #
    wa
    #
    @11
    cgbo
    wcel
    #
    wi
    #
    vn
    codd
    wral
    #
    wa
    #
    vm
    cn
    wrex
    @0
    @3
    c8
    c8
    8nn0
    8nn
    decnncl
    @1
    cn
    wcel
    #
    @2
    cn0
    wcel
    #
    @3
    cn
    wcel
    10nn
    c2
    c9
    2nn0
    9nn0
    deccl
    #
    @1
    @2
    nnexpcl
    mp2an
    #
    nnmulcli
    @5
    @18
    @8
    @4
    clt
    wbr
    #
    @12
    @11
    @4
    clt
    wbr
    #
    wa
    #
    @15
    wi
    #
    vn
    codd
    wral
    #
    wa
    #
    vm
    @4
    cn
    @5
    id
    @9
    @4
    wceq
    #
    @18
    @28
    wb
    @5
    @29
    @10
    @23
    @17
    @27
    @9
    @4
    @8
    clt
    breq2
    @29
    @16
    @26
    vn
    codd
    @29
    @14
    @25
    @15
    @29
    @13
    @24
    @12
    @9
    @4
    @11
    clt
    breq2
    anbi2d
    imbi1d
    ralbidv
    anbi12d
    adantl
    @5
    @27
    @23
    @5
    @26
    vn
    codd
    @5
    @11
    codd
    wcel
    #
    wa
    #
    @25
    @15
    @31
    @25
    wa
    @30
    @12
    @24
    @15
    @5
    @30
    @25
    simplr
    @31
    @12
    @24
    simprl
    @31
    @12
    @24
    simprr
    @11
    tgblthelfgott
    syl3anc
    ex
    ralrimiva
    @8
    @8
    c8
    @3
    cmul
    co
    #
    caddc
    co
    #
    @4
    clt
    cc0
    @32
    clt
    wbr
    @8
    @33
    clt
    wbr
    @32
    c8
    @3
    8nn
    @22
    nnmulcli
    #
    nngt0i
    @32
    @8
    @32
    @34
    nnrei
    @8
    c8
    @7
    8nn
    @19
    @6
    cn0
    wcel
    @7
    cn
    wcel
    10nn
    c3
    cc0
    3nn0
    0nn0
    deccl
    @1
    @6
    nnexpcl
    mp2an
    #
    nnmulcli
    nnrei
    ltaddposi
    mpbi
    @4
    @1
    c8
    cmul
    co
    #
    c8
    caddc
    co
    #
    @3
    cmul
    co
    @36
    @3
    cmul
    co
    #
    @32
    caddc
    co
    #
    @33
    @0
    @37
    @3
    cmul
    c8
    c8
    dfdec10
    oveq1i
    @36
    c8
    @3
    @36
    @1
    c8
    10nn
    8nn
    nnmulcli
    nncni
    #
    8cn
    @3
    @22
    nncni
    #
    adddiri
    @39
    @1
    @2
    c1
    caddc
    co
    #
    cexp
    co
    #
    c8
    cmul
    co
    #
    @32
    caddc
    co
    @7
    c8
    cmul
    co
    #
    @32
    caddc
    co
    #
    @33
    @38
    @44
    @32
    caddc
    @38
    @3
    @36
    cmul
    co
    @3
    @1
    cmul
    co
    #
    c8
    cmul
    co
    @44
    @36
    @3
    @40
    @41
    mulcomi
    @3
    @1
    c8
    @41
    @1
    10nn
    nncni
    8cn
    mulassi
    @47
    @43
    c8
    cmul
    @43
    @47
    @19
    @43
    @47
    wceq
    10nn
    @19
    @1
    @2
    @1
    nncn
    @20
    @19
    @21
    a1i
    expp1d
    ax-mp
    eqcomi
    oveq1i
    3eqtr2i
    oveq1i
    @44
    @45
    @32
    caddc
    @43
    @7
    c8
    cmul
    @42
    @6
    @1
    cexp
    c2
    c3
    @2
    2nn0
    2p1e3
    @2
    eqid
    decsucc
    oveq2i
    oveq1i
    oveq1i
    @7
    cc
    wcel
    #
    c8
    cc
    wcel
    #
    @46
    @33
    wceq
    @7
    @35
    nncni
    8cn
    @48
    @49
    wa
    @45
    @8
    @32
    caddc
    @7
    c8
    mulcom
    oveq1d
    mp2an
    3eqtri
    3eqtri
    breqtrri
    jctil
    rspcedvd
    ax-mp
end
