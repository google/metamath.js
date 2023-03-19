include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "wa.mm"
include "c3.mm"
include "cneg.mm"
include "cop.mm"
include "csn.mm"
include "cdif.mm"
include "cc0.mm"
include "cxp.mm"
include "cun.mm"
include "caddc.mm"
include "wceq.mm"
include "wn.mm"
include "wne.mm"
include "crn.mm"
include "cpr.mm"
include "wo.mm"
include "c2.mm"
include "2ne0.mm"
include "neii.mm"
include "eqcom.mm"
include "1pneg1e0.mm"
include "eqcomi.mm"
include "df-2.mm"
include "eqeq12i.mm"
include "ax-1cn.mm"
include "neg1cn.mm"
include "addcani.mm"
include "3bitri.mm"
include "mtbi.mm"
include "intnanr.mm"
include "ax-1ne0.mm"
include "cc.mm"
include "wb.mm"
include "negeq0.mm"
include "ax-mp.mm"
include "pm3.2ni.mm"
include "negex.mm"
include "c0ex.mm"
include "1ex.mm"
include "preq12b.mm"
include "mtbir.mm"
include "3ex.mm"
include "rnsnop.mm"
include "a1i.mm"
include "c0.mm"
include "cuz.mm"
include "cfv.mm"
include "elnnuz.mm"
include "eluzfz1.mm"
include "sylbi.mm"
include "df-3.mm"
include "1e0p1.mm"
include "2cn.mm"
include "0cn.mm"
include "addcan2i.mm"
include "bitri.mm"
include "necon3bii.mm"
include "mpbir.mm"
include "necomi.mm"
include "jctir.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "adantr.mm"
include "ne0i.mm"
include "rnxp.mm"
include "3syl.mm"
include "uneq12d.mm"
include "rnun.mm"
include "df-pr.mm"
include "3eqtr4g.mm"
include "ovex.mm"
include "cz.mm"
include "wss.mm"
include "nnz.mm"
include "fzssp1.mm"
include "zcn.mm"
include "npcan1.mm"
include "oveq2d.mm"
include "syl.mm"
include "syl5sseq.mm"
include "sselda.mm"
include "cr.mm"
include "elfzelz.mm"
include "zred.mm"
include "id.mm"
include "ltp1.mm"
include "ltned.mm"
include "adantl.mm"
include "sylanbrc.mm"
include "eqeq12d.mm"
include "mtbiri.mm"
include "rneq.mm"
include "nsyl.mm"
include "necon3abii.mm"

theorem axlowdimlem13
  let cP: class P
  let cQ: class Q
  let cI: class I
  let cN: class N
  assume axlowdimlem13.1: |- P = ( { <. 3 , -u 1 >. } u. ( ( ( 1 ... N ) \ { 3 } ) X. { 0 } ) )
  assume axlowdimlem13.2: |- Q = ( { <. ( I + 1 ) , 1 >. } u. ( ( ( 1 ... N ) \ { ( I + 1 ) } ) X. { 0 } ) )


  assert |- ( ( N e. NN /\ I e. ( 1 ... ( N - 1 ) ) ) -> P =/= Q )

  proof
    cN
    cn
    wcel
    #
    cI
    c1
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    c3
    c1
    cneg
    #
    cop
    csn
    #
    c1
    cN
    cfz
    co
    #
    c3
    csn
    cdif
    #
    cc0
    csn
    #
    cxp
    #
    cun
    #
    cI
    c1
    caddc
    co
    #
    c1
    cop
    csn
    #
    @7
    @12
    csn
    cdif
    #
    @9
    cxp
    #
    cun
    #
    wceq
    #
    wn
    cP
    cQ
    wne
    @4
    @11
    crn
    #
    @16
    crn
    #
    wceq
    #
    @17
    @4
    @20
    @5
    cc0
    cpr
    #
    c1
    cc0
    cpr
    #
    wceq
    #
    @23
    @5
    c1
    wceq
    #
    cc0
    cc0
    wceq
    #
    wa
    #
    @5
    cc0
    wceq
    #
    cc0
    c1
    wceq
    #
    wa
    #
    wo
    @26
    @29
    @24
    @25
    c2
    cc0
    wceq
    #
    @24
    c2
    cc0
    2ne0
    neii
    @30
    cc0
    c2
    wceq
    c1
    @5
    caddc
    co
    #
    c1
    c1
    caddc
    co
    #
    wceq
    @24
    c2
    cc0
    eqcom
    cc0
    @31
    c2
    @32
    @31
    cc0
    1pneg1e0
    eqcomi
    df-2
    eqeq12i
    c1
    @5
    c1
    ax-1cn
    neg1cn
    ax-1cn
    addcani
    3bitri
    mtbi
    intnanr
    @27
    @28
    c1
    cc0
    wceq
    #
    @27
    c1
    cc0
    ax-1ne0
    neii
    c1
    cc
    wcel
    @33
    @27
    wb
    ax-1cn
    c1
    negeq0
    ax-mp
    mtbi
    intnanr
    pm3.2ni
    @5
    cc0
    c1
    cc0
    c1
    negex
    c0ex
    1ex
    c0ex
    preq12b
    mtbir
    @4
    @18
    @21
    @19
    @22
    @4
    @6
    crn
    #
    @10
    crn
    #
    cun
    @5
    csn
    #
    @9
    cun
    @18
    @21
    @4
    @34
    @36
    @35
    @9
    @34
    @36
    wceq
    @4
    c3
    @5
    3ex
    rnsnop
    a1i
    @4
    c1
    @8
    wcel
    #
    @8
    c0
    wne
    @35
    @9
    wceq
    @0
    @37
    @3
    @0
    c1
    @7
    wcel
    #
    c1
    c3
    wne
    #
    wa
    @37
    @0
    @38
    @39
    @0
    cN
    c1
    cuz
    cfv
    wcel
    @38
    cN
    elnnuz
    c1
    cN
    eluzfz1
    sylbi
    c3
    c1
    c3
    c1
    wne
    c2
    cc0
    wne
    2ne0
    c3
    c1
    c2
    cc0
    c3
    c1
    wceq
    c2
    c1
    caddc
    co
    #
    cc0
    c1
    caddc
    co
    #
    wceq
    @30
    c3
    @40
    c1
    @41
    df-3
    1e0p1
    eqeq12i
    c2
    cc0
    c1
    2cn
    0cn
    ax-1cn
    addcan2i
    bitri
    necon3bii
    mpbir
    necomi
    jctir
    c1
    @7
    c3
    eldifsn
    sylibr
    adantr
    @8
    c1
    ne0i
    @8
    @9
    rnxp
    3syl
    uneq12d
    @6
    @10
    rnun
    @5
    cc0
    df-pr
    3eqtr4g
    @4
    @13
    crn
    #
    @15
    crn
    #
    cun
    c1
    csn
    #
    @9
    cun
    @19
    @22
    @4
    @42
    @44
    @43
    @9
    @42
    @44
    wceq
    @4
    @12
    c1
    cI
    c1
    caddc
    ovex
    rnsnop
    a1i
    @4
    cI
    @14
    wcel
    #
    @14
    c0
    wne
    @43
    @9
    wceq
    @4
    cI
    @7
    wcel
    cI
    @12
    wne
    #
    @45
    @0
    @2
    @7
    cI
    @0
    cN
    cz
    wcel
    #
    @2
    @7
    wss
    cN
    nnz
    @47
    c1
    @1
    c1
    caddc
    co
    #
    cfz
    co
    #
    @2
    @7
    c1
    @1
    fzssp1
    @47
    cN
    cc
    wcel
    #
    @49
    @7
    wceq
    cN
    zcn
    @50
    @48
    cN
    c1
    cfz
    cN
    npcan1
    oveq2d
    syl
    syl5sseq
    syl
    sselda
    @3
    @46
    @0
    @3
    cI
    cr
    wcel
    #
    @46
    @3
    cI
    cI
    c1
    @1
    elfzelz
    zred
    @51
    cI
    @12
    @51
    id
    cI
    ltp1
    ltned
    syl
    adantl
    cI
    @7
    @12
    eldifsn
    sylanbrc
    @14
    cI
    ne0i
    @14
    @9
    rnxp
    3syl
    uneq12d
    @13
    @15
    rnun
    c1
    cc0
    df-pr
    3eqtr4g
    eqeq12d
    mtbiri
    @11
    @16
    rneq
    nsyl
    @17
    cP
    cQ
    cP
    @11
    cQ
    @16
    axlowdimlem13.1
    axlowdimlem13.2
    eqeq12i
    necon3abii
    sylibr
end
