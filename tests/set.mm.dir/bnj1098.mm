include "cv.mm"
include "c0.mm"
include "wne.mm"
include "wel.mm"
include "wcel.mm"
include "w3a.mm"
include "com.mm"
include "csuc.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "wrex.mm"
include "wex.mm"
include "3anrev.mm"
include "df-3an.mm"
include "bitri.mm"
include "simpr.mm"
include "bnj923.mm"
include "adantr.mm"
include "elnn.mm"
include "syl2anc.mm"
include "anim1i.mm"
include "sylbi.mm"
include "nnsuc.mm"
include "syl.mm"
include "df-rex.mm"
include "imbi2i.mm"
include "19.37v.mm"
include "bitr4i.mm"
include "mpbi.mm"
include "ancr.mm"
include "bnj101.mm"
include "vex.mm"
include "bnj216.mm"
include "ad2antlr.mm"
include "simpr2.mm"
include "word.mm"
include "3simpc.mm"
include "ancomd.mm"
include "adantl.mm"
include "nnord.mm"
include "ordtr1.mm"
include "4syl.mm"
include "mp2and.mm"
include "simplr.mm"
include "jca.mm"
include "bnj1023.mm"

theorem bnj1098
  let cD: class D
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  assume bnj1098.1: |- D = ( _om \ { (/) } )

  disjoint D j
  disjoint i j
  disjoint j n
  assert |- E. j ( ( i =/= (/) /\ i e. n /\ n e. D ) -> ( j e. n /\ i = suc j ) )

  proof
    vi
    cv
    #
    c0
    wne
    #
    vi
    vn
    wel
    #
    vn
    cv
    #
    cD
    wcel
    #
    w3a
    #
    vj
    cv
    #
    com
    wcel
    #
    @0
    @6
    csuc
    wceq
    #
    wa
    #
    @5
    wa
    #
    vj
    vn
    wel
    #
    @8
    wa
    vj
    @5
    @9
    wi
    #
    @5
    @10
    wi
    vj
    @5
    @8
    vj
    com
    wrex
    #
    wi
    #
    @12
    vj
    wex
    #
    @5
    @0
    com
    wcel
    #
    @1
    wa
    #
    @13
    @5
    @4
    @2
    wa
    #
    @1
    wa
    #
    @17
    @5
    @4
    @2
    @1
    w3a
    @19
    @1
    @2
    @4
    3anrev
    @4
    @2
    @1
    df-3an
    bitri
    @18
    @16
    @1
    @18
    @2
    @3
    com
    wcel
    #
    @16
    @4
    @2
    simpr
    @4
    @20
    @2
    cD
    vn
    bnj1098.1
    bnj923
    adantr
    #
    @0
    @3
    elnn
    syl2anc
    anim1i
    sylbi
    vj
    @0
    nnsuc
    syl
    @14
    @5
    @9
    vj
    wex
    #
    wi
    @15
    @13
    @22
    @5
    @8
    vj
    com
    df-rex
    imbi2i
    @5
    @9
    vj
    19.37v
    bitr4i
    mpbi
    @5
    @9
    ancr
    bnj101
    @10
    @11
    @8
    @10
    vj
    vi
    wel
    #
    @2
    @11
    @8
    @23
    @7
    @5
    @0
    @6
    vj
    vex
    bnj216
    ad2antlr
    @9
    @1
    @2
    @4
    simpr2
    @10
    @18
    @20
    @3
    word
    @23
    @2
    wa
    @11
    wi
    @5
    @18
    @9
    @5
    @2
    @4
    @1
    @2
    @4
    3simpc
    ancomd
    adantl
    @21
    @3
    nnord
    @6
    @0
    @3
    ordtr1
    4syl
    mp2and
    @7
    @8
    @5
    simplr
    jca
    bnj1023
end
