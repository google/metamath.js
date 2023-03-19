include "cuspgr.mm"
include "wcel.mm"
include "cword.mm"
include "c2.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "cdm.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "wceq.mm"
include "cfzo.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "clsw.mm"
include "cmin.mm"
include "cop.mm"
include "csubstr.mm"
include "crn.mm"
include "cclwlks.mm"
include "cclwwlk.mm"
include "cedg.mm"
include "wf1.mm"
include "wb.mm"
include "wf1o.mm"
include "uspgrf1oedg.mm"
include "f1of1.mm"
include "syl.mm"
include "clwlkclwwlklem3.mm"
include "syl3an1.mm"
include "cn0.mm"
include "lencl.mm"
include "ige2m1fz.mm"
include "sylan.mm"
include "swrd0len.mm"
include "syldan.mm"
include "nn0cnd.mm"
include "1cnd.mm"
include "subcld.mm"
include "subid1d.mm"
include "eqcomd.mm"
include "adantr.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "c0.mm"
include "wne.mm"
include "simpll.mm"
include "wrdlenge2n0.mm"
include "cz.mm"
include "nn0z.mm"
include "peano2zm.mm"
include "elfzom1elfzo.mm"
include "swrdtrcfv.mm"
include "syl3anc.mm"
include "elfzom1elp1fzo.mm"
include "preq12d.mm"
include "eleq1d.mm"
include "ex.mm"
include "sylbid.mm"
include "imp.mm"
include "raleqbidva.mm"
include "swrdtrcfvl.mm"
include "swrdtrcfv0.mm"
include "anbi12d.mm"
include "bicomd.mm"
include "3adant1.mm"
include "swrdcl.mm"
include "3ad2ant2.mm"
include "3biant1d.mm"
include "bitrd.mm"
include "anbi2d.mm"
include "cupgr.mm"
include "uspgrupgr.mm"
include "isclwlkupgr.mm"
include "3an4anass.mm"
include "syl6bbr.mm"
include "exbidv.mm"
include "3adant3.mm"
include "eqid.mm"
include "isclwwlk.mm"
include "cn.mm"
include "simpl.mm"
include "nn0ge2m1nn.mm"
include "wi.mm"
include "nn0re.mm"
include "lem1d.mm"
include "a1d.mm"
include "3jca.mm"
include "swrdn0.mm"
include "biantrud.mm"
include "3anbi1d.mm"
include "syl5bb.mm"
include "biid.mm"
include "ciedg.mm"
include "edgval.mm"
include "eqcomi.mm"
include "rneqi.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "ralbii.mm"
include "3anbi123i.mm"
include "syl6bb.mm"
include "3bitr4d.mm"

theorem clwlkclwwlk
  let cP: class P
  let vf: setvar f
  let cE: class E
  let cG: class G
  let cV: class V
  let vi: setvar i
  let vx: setvar x
  let cR: class R
  let cF: class F
  assume clwlkclwwlk.v: |- V = ( Vtx ` G )
  assume clwlkclwwlk.e: |- E = ( iEdg ` G )

  disjoint E f
  disjoint P f
  disjoint V f
  disjoint G f
  disjoint E i
  disjoint E x
  disjoint f i
  disjoint f x
  disjoint i x
  disjoint P i
  disjoint P x
  disjoint R f
  disjoint R i
  disjoint R x
  disjoint V i
  disjoint V x
  disjoint F i
  disjoint G i
  assert |- ( ( G e. USPGraph /\ P e. Word V /\ 2 <_ ( # ` P ) ) -> ( E. f f ( ClWalks ` G ) P <-> ( ( lastS ` P ) = ( P ` 0 ) /\ ( P substr <. 0 , ( ( # ` P ) - 1 ) >. ) e. ( ClWWalks ` G ) ) ) )

  proof
    cG
    cuspgr
    wcel
    #
    cP
    cV
    cword
    #
    wcel
    #
    c2
    cP
    chash
    cfv
    #
    cle
    wbr
    #
    w3a
    #
    vf
    cv
    #
    cE
    cdm
    #
    cword
    wcel
    #
    cc0
    @6
    chash
    cfv
    #
    cfz
    co
    cV
    cP
    wf
    #
    vi
    cv
    #
    @6
    cfv
    cE
    cfv
    @11
    cP
    cfv
    #
    @11
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    wceq
    vi
    cc0
    @9
    cfzo
    co
    wral
    #
    w3a
    cc0
    cP
    cfv
    #
    @9
    cP
    cfv
    wceq
    #
    wa
    #
    vf
    wex
    #
    cP
    clsw
    cfv
    @17
    wceq
    #
    cP
    cc0
    @3
    c1
    cmin
    co
    #
    cop
    csubstr
    co
    #
    @1
    wcel
    #
    @11
    @23
    cfv
    #
    @13
    @23
    cfv
    #
    cpr
    #
    cE
    crn
    #
    wcel
    #
    vi
    cc0
    @23
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    @23
    clsw
    cfv
    #
    cc0
    @23
    cfv
    #
    cpr
    #
    @28
    wcel
    #
    w3a
    #
    wa
    #
    @6
    cP
    cG
    cclwlks
    cfv
    wbr
    #
    vf
    wex
    #
    @21
    @23
    cG
    cclwwlk
    cfv
    wcel
    #
    wa
    @5
    @20
    @21
    @15
    @28
    wcel
    #
    vi
    cc0
    @22
    cc0
    cmin
    co
    #
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    @3
    c2
    cmin
    co
    cP
    cfv
    #
    @17
    cpr
    #
    @28
    wcel
    #
    wa
    #
    wa
    #
    @39
    @0
    @7
    cG
    cedg
    cfv
    #
    cE
    wf1
    #
    @2
    @4
    @20
    @52
    wb
    @0
    @7
    @53
    cE
    wf1o
    @54
    cE
    cG
    clwlkclwwlk.e
    uspgrf1oedg
    @7
    @53
    cE
    f1of1
    syl
    cP
    @53
    vf
    vi
    cE
    cV
    clwlkclwwlklem3
    syl3an1
    @5
    @51
    @38
    @21
    @5
    @51
    @33
    @37
    wa
    #
    @38
    @2
    @4
    @51
    @55
    wb
    @0
    @2
    @4
    wa
    #
    @55
    @51
    @56
    @33
    @47
    @37
    @50
    @56
    @29
    @43
    vi
    @32
    @46
    @56
    @31
    @45
    cc0
    cfzo
    @56
    @30
    @44
    c1
    cmin
    @56
    @30
    @22
    @44
    @2
    @4
    @22
    cc0
    @3
    cfz
    co
    wcel
    #
    @30
    @22
    wceq
    @2
    @3
    cn0
    wcel
    #
    @4
    @57
    cV
    cP
    lencl
    #
    @3
    ige2m1fz
    sylan
    cV
    cP
    @22
    swrd0len
    syldan
    #
    @2
    @22
    @44
    wceq
    @4
    @2
    @44
    @22
    @2
    @22
    @2
    @3
    c1
    @2
    @3
    @59
    nn0cnd
    @2
    1cnd
    subcld
    subid1d
    eqcomd
    adantr
    eqtrd
    oveq1d
    oveq2d
    @56
    @11
    @32
    wcel
    #
    @29
    @43
    wb
    #
    @56
    @61
    @11
    cc0
    @22
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wcel
    #
    @62
    @56
    @32
    @64
    @11
    @56
    @31
    @63
    cc0
    cfzo
    @56
    @30
    @22
    c1
    cmin
    @60
    oveq1d
    oveq2d
    eleq2d
    @56
    @65
    @62
    @56
    @65
    wa
    #
    @27
    @15
    @28
    @66
    @25
    @12
    @26
    @14
    @66
    @2
    cP
    c0
    wne
    #
    @11
    cc0
    @22
    cfzo
    co
    #
    wcel
    #
    @25
    @12
    wceq
    @2
    @4
    @65
    simpll
    #
    @56
    @67
    @65
    cV
    cP
    wrdlenge2n0
    adantr
    #
    @56
    @22
    cz
    wcel
    #
    @65
    @69
    @2
    @72
    @4
    @2
    @58
    @72
    @59
    @58
    @3
    cz
    wcel
    @72
    @3
    nn0z
    @3
    peano2zm
    syl
    #
    syl
    adantr
    @11
    @22
    elfzom1elfzo
    sylan
    @11
    cV
    cP
    swrdtrcfv
    syl3anc
    @66
    @2
    @67
    @13
    @68
    wcel
    #
    @26
    @14
    wceq
    @70
    @71
    @56
    @58
    @65
    @74
    @2
    @58
    @4
    @59
    adantr
    @58
    @72
    @65
    @74
    @73
    @11
    @22
    elfzom1elp1fzo
    sylan
    sylan
    @13
    cV
    cP
    swrdtrcfv
    syl3anc
    preq12d
    eleq1d
    ex
    sylbid
    imp
    raleqbidva
    @56
    @36
    @49
    @28
    @56
    @34
    @48
    @35
    @17
    cV
    cP
    swrdtrcfvl
    cV
    cP
    swrdtrcfv0
    preq12d
    eleq1d
    anbi12d
    bicomd
    3adant1
    @5
    @37
    @33
    @24
    @2
    @0
    @24
    @4
    cV
    cP
    cc0
    @22
    swrdcl
    3ad2ant2
    3biant1d
    bitrd
    anbi2d
    bitrd
    @0
    @2
    @41
    @20
    wb
    @4
    @0
    @2
    wa
    @40
    @19
    vf
    @0
    @40
    @19
    wb
    #
    @2
    @0
    cG
    cupgr
    wcel
    #
    @75
    cG
    uspgrupgr
    @76
    @40
    @8
    @10
    wa
    @16
    @18
    wa
    wa
    @19
    cP
    vi
    @6
    cG
    cE
    cV
    clwlkclwwlk.v
    clwlkclwwlk.e
    isclwlkupgr
    @8
    @10
    @16
    @18
    3an4anass
    syl6bbr
    syl
    adantr
    exbidv
    3adant3
    @5
    @42
    @38
    @21
    @5
    @42
    @24
    @27
    @53
    wcel
    #
    vi
    @32
    wral
    #
    @36
    @53
    wcel
    #
    w3a
    #
    @38
    @42
    @24
    @23
    c0
    wne
    #
    wa
    #
    @78
    @79
    w3a
    @5
    @80
    vi
    @53
    cG
    cV
    @23
    clwlkclwwlk.v
    @53
    eqid
    isclwwlk
    @5
    @82
    @24
    @78
    @79
    @5
    @24
    @82
    @5
    @81
    @24
    @5
    @2
    @22
    cn
    wcel
    #
    @22
    @3
    cle
    wbr
    #
    w3a
    #
    @81
    @2
    @4
    @85
    @0
    @56
    @2
    @83
    @84
    @2
    @4
    simpl
    @2
    @58
    @4
    @83
    @59
    @3
    nn0ge2m1nn
    sylan
    @2
    @4
    @84
    @2
    @58
    @4
    @84
    wi
    @59
    @58
    @84
    @4
    @58
    @3
    @3
    nn0re
    lem1d
    a1d
    syl
    imp
    3jca
    3adant1
    @22
    cV
    cP
    swrdn0
    syl
    biantrud
    bicomd
    3anbi1d
    syl5bb
    @24
    @24
    @78
    @33
    @79
    @37
    @24
    biid
    @77
    @29
    vi
    @32
    @53
    @28
    @27
    @53
    cG
    ciedg
    cfv
    #
    crn
    @28
    cG
    edgval
    @86
    cE
    cE
    @86
    clwlkclwwlk.e
    eqcomi
    rneqi
    eqtri
    #
    eleq2i
    ralbii
    @53
    @28
    @36
    @87
    eleq2i
    3anbi123i
    syl6bb
    anbi2d
    3bitr4d
end
