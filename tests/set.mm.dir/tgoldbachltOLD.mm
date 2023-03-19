include "c8.mm"
include "cdc.mm"
include "c10.mm"
include "c2.mm"
include "c9.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cn.mm"
include "wcel.mm"
include "c3.mm"
include "cc0.mm"
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
include "10nnOLD.mm"
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
include "tgblthelfgottOLD.mm"
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
include "dfdecOLD.mm"
include "oveq1i.mm"
include "nncni.mm"
include "8cn.mm"
include "adddiri.mm"
include "c1.mm"
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

theorem tgoldbachltOLD
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
  assert |- E. m e. NN ( ( 8 x. ( 10 ^ ; 3 0 ) ) < m /\ A. n e. Odd ( ( 7 < n /\ n < m ) -> n e. GoldbachOdd ) )

  proof
    c8
    c8
    cdc
    #
    c10
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
    c10
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
    @10
    @8
    clt
    wbr
    #
    wa
    #
    @10
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
    @2
    c8
    c8
    8nn0
    8nn
    decnncl
    c10
    cn
    wcel
    #
    @1
    cn0
    wcel
    #
    @2
    cn
    wcel
    10nnOLD
    c2
    c9
    2nn0
    9nn0
    deccl
    #
    c10
    @1
    nnexpcl
    mp2an
    #
    nnmulcli
    @4
    @17
    @7
    @3
    clt
    wbr
    #
    @11
    @10
    @3
    clt
    wbr
    #
    wa
    #
    @14
    wi
    #
    vn
    codd
    wral
    #
    wa
    #
    vm
    @3
    cn
    @4
    id
    @8
    @3
    wceq
    #
    @17
    @27
    wb
    @4
    @28
    @9
    @22
    @16
    @26
    @8
    @3
    @7
    clt
    breq2
    @28
    @15
    @25
    vn
    codd
    @28
    @13
    @24
    @14
    @28
    @12
    @23
    @11
    @8
    @3
    @10
    clt
    breq2
    anbi2d
    imbi1d
    ralbidv
    anbi12d
    adantl
    @4
    @26
    @22
    @4
    @25
    vn
    codd
    @4
    @10
    codd
    wcel
    #
    wa
    #
    @24
    @14
    @30
    @24
    wa
    @29
    @11
    @23
    @14
    @4
    @29
    @24
    simplr
    @30
    @11
    @23
    simprl
    @30
    @11
    @23
    simprr
    @10
    tgblthelfgottOLD
    syl3anc
    ex
    ralrimiva
    @7
    @7
    c8
    @2
    cmul
    co
    #
    caddc
    co
    #
    @3
    clt
    cc0
    @31
    clt
    wbr
    @7
    @32
    clt
    wbr
    @31
    c8
    @2
    8nn
    @21
    nnmulcli
    #
    nngt0i
    @31
    @7
    @31
    @33
    nnrei
    @7
    c8
    @6
    8nn
    @18
    @5
    cn0
    wcel
    @6
    cn
    wcel
    10nnOLD
    c3
    cc0
    3nn0
    0nn0
    deccl
    c10
    @5
    nnexpcl
    mp2an
    #
    nnmulcli
    nnrei
    ltaddposi
    mpbi
    @3
    c10
    c8
    cmul
    co
    #
    c8
    caddc
    co
    #
    @2
    cmul
    co
    @35
    @2
    cmul
    co
    #
    @31
    caddc
    co
    #
    @32
    @0
    @36
    @2
    cmul
    c8
    c8
    dfdecOLD
    oveq1i
    @35
    c8
    @2
    @35
    c10
    c8
    10nnOLD
    8nn
    nnmulcli
    nncni
    #
    8cn
    @2
    @21
    nncni
    #
    adddiri
    @38
    c10
    @1
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
    @31
    caddc
    co
    @6
    c8
    cmul
    co
    #
    @31
    caddc
    co
    #
    @32
    @37
    @43
    @31
    caddc
    @37
    @2
    @35
    cmul
    co
    @2
    c10
    cmul
    co
    #
    c8
    cmul
    co
    @43
    @35
    @2
    @39
    @40
    mulcomi
    @2
    c10
    c8
    @40
    c10
    10nnOLD
    nncni
    8cn
    mulassi
    @46
    @42
    c8
    cmul
    @42
    @46
    @18
    @42
    @46
    wceq
    10nnOLD
    @18
    c10
    @1
    c10
    nncn
    @19
    @18
    @20
    a1i
    expp1d
    ax-mp
    eqcomi
    oveq1i
    3eqtr2i
    oveq1i
    @43
    @44
    @31
    caddc
    @42
    @6
    c8
    cmul
    @41
    @5
    c10
    cexp
    c2
    c3
    @1
    2nn0
    2p1e3
    @1
    eqid
    decsucc
    oveq2i
    oveq1i
    oveq1i
    @6
    cc
    wcel
    #
    c8
    cc
    wcel
    #
    @45
    @32
    wceq
    @6
    @34
    nncni
    8cn
    @47
    @48
    wa
    @44
    @7
    @31
    caddc
    @6
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
