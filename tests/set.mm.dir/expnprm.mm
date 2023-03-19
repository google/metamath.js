include "cq.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wa.mm"
include "c1.mm"
include "wne.mm"
include "cexp.mm"
include "co.mm"
include "cprime.mm"
include "wn.mm"
include "cn.mm"
include "eluz2b3.mm"
include "simprbi.mm"
include "adantl.mm"
include "cdvds.mm"
include "wbr.mm"
include "wceq.mm"
include "cpc.mm"
include "cmul.mm"
include "cz.mm"
include "eluzelz.mm"
include "ad2antlr.mm"
include "cc0.mm"
include "simpr.mm"
include "simpll.mm"
include "prmnn.mm"
include "nnne0d.mm"
include "eluz2nn.mm"
include "0expd.mm"
include "neeqtrrd.mm"
include "oveq1.mm"
include "necon3i.mm"
include "syl.mm"
include "pcqcl.mm"
include "syl12anc.mm"
include "dvdsmul1.mm"
include "syl2anc.mm"
include "nncnd.mm"
include "exp1d.mm"
include "oveq2d.mm"
include "1z.mm"
include "pcid.mm"
include "sylancl.mm"
include "pcexp.mm"
include "syl121anc.mm"
include "3eqtr3rd.mm"
include "breqtrd.mm"
include "ex.mm"
include "cn0.mm"
include "wb.mm"
include "nnnn0d.mm"
include "dvds1.mm"
include "sylibd.mm"
include "necon3ad.mm"
include "mpd.mm"

theorem expnprm
  let cA: class A
  let cN: class N
  let vp: setvar p


  assert |- ( ( A e. QQ /\ N e. ( ZZ>= ` 2 ) ) -> -. ( A ^ N ) e. Prime )

  proof
    cA
    cq
    wcel
    #
    cN
    c2
    cuz
    cfv
    wcel
    #
    wa
    #
    cN
    c1
    wne
    #
    cA
    cN
    cexp
    co
    #
    cprime
    wcel
    #
    wn
    @1
    @3
    @0
    @1
    cN
    cn
    wcel
    #
    @3
    cN
    eluz2b3
    simprbi
    adantl
    @2
    @5
    cN
    c1
    @2
    @5
    cN
    c1
    cdvds
    wbr
    #
    cN
    c1
    wceq
    #
    @2
    @5
    @7
    @2
    @5
    wa
    #
    cN
    cN
    @4
    cA
    cpc
    co
    #
    cmul
    co
    #
    c1
    cdvds
    @9
    cN
    cz
    wcel
    #
    @10
    cz
    wcel
    #
    cN
    @11
    cdvds
    wbr
    @1
    @12
    @0
    @5
    c2
    cN
    eluzelz
    ad2antlr
    #
    @9
    @5
    @0
    cA
    cc0
    wne
    #
    @13
    @2
    @5
    simpr
    #
    @0
    @1
    @5
    simpll
    #
    @9
    @4
    cc0
    cN
    cexp
    co
    #
    wne
    @15
    @9
    @4
    cc0
    @18
    @9
    @4
    @5
    @4
    cn
    wcel
    @2
    @4
    prmnn
    adantl
    #
    nnne0d
    @9
    cN
    @1
    @6
    @0
    @5
    cN
    eluz2nn
    #
    ad2antlr
    0expd
    neeqtrrd
    cA
    cc0
    @4
    @18
    cA
    cc0
    cN
    cexp
    oveq1
    necon3i
    syl
    #
    @4
    cA
    pcqcl
    syl12anc
    cN
    @10
    dvdsmul1
    syl2anc
    @9
    @4
    @4
    c1
    cexp
    co
    #
    cpc
    co
    #
    @4
    @4
    cpc
    co
    #
    c1
    @11
    @9
    @22
    @4
    @4
    cpc
    @9
    @4
    @9
    @4
    @19
    nncnd
    exp1d
    oveq2d
    @9
    @5
    c1
    cz
    wcel
    @23
    c1
    wceq
    @16
    1z
    c1
    @4
    pcid
    sylancl
    @9
    @5
    @0
    @15
    @12
    @24
    @11
    wceq
    @16
    @17
    @21
    @14
    cA
    @4
    cN
    pcexp
    syl121anc
    3eqtr3rd
    breqtrd
    ex
    @2
    cN
    cn0
    wcel
    @7
    @8
    wb
    @2
    cN
    @1
    @6
    @0
    @20
    adantl
    nnnn0d
    cN
    dvds1
    syl
    sylibd
    necon3ad
    mpd
end
