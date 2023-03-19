include "cusgr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "weu.mm"
include "wreu.mm"
include "cnbgr.mm"
include "co.mm"
include "simpll.mm"
include "eleq2i.mm"
include "wb.mm"
include "nbgrsym.mm"
include "a1i.mm"
include "biimpd.mm"
include "syl5bi.mm"
include "imp.mm"
include "nbusgredgeu.mm"
include "syl2anc.mm"
include "df-reu.mm"
include "sylib.mm"
include "anass.mm"
include "prid1g.mm"
include "ad2antlr.mm"
include "eleq2.mm"
include "syl5ibrcom.mm"
include "pm4.71rd.mm"
include "bicomd.mm"
include "anbi2d.mm"
include "syl5bb.mm"
include "eubidv.mm"
include "mpbird.mm"
include "elrab2.mm"
include "anbi1i.mm"
include "eubii.mm"
include "bitri.mm"
include "sylibr.mm"

theorem nbusgredgeu0
  let cU: class U
  let ve: setvar e
  let vi: setvar i
  let cE: class E
  let cG: class G
  let cI: class I
  let cM: class M
  let cN: class N
  let cV: class V
  assume nbusgrf1o1.v: |- V = ( Vtx ` G )
  assume nbusgrf1o1.e: |- E = ( Edg ` G )
  assume nbusgrf1o1.n: |- N = ( G NeighbVtx U )
  assume nbusgrf1o1.i: |- I = { e e. E | U e. e }

  disjoint E i
  disjoint E e
  disjoint e i
  disjoint G i
  disjoint M i
  disjoint N i
  disjoint U i
  disjoint U e
  disjoint V i
  assert |- ( ( ( G e. USGraph /\ U e. V ) /\ M e. N ) -> E! i e. I i = { U , M } )

  proof
    cG
    cusgr
    wcel
    #
    cU
    cV
    wcel
    #
    wa
    #
    cM
    cN
    wcel
    #
    wa
    #
    vi
    cv
    #
    cE
    wcel
    #
    cU
    @5
    wcel
    #
    wa
    #
    @5
    cU
    cM
    cpr
    #
    wceq
    #
    wa
    #
    vi
    weu
    #
    @10
    vi
    cI
    wreu
    #
    @4
    @12
    @6
    @10
    wa
    #
    vi
    weu
    #
    @4
    @10
    vi
    cE
    wreu
    #
    @15
    @4
    @0
    cU
    cG
    cM
    cnbgr
    co
    wcel
    #
    @16
    @0
    @1
    @3
    simpll
    @2
    @3
    @17
    @3
    cM
    cG
    cU
    cnbgr
    co
    #
    wcel
    #
    @2
    @17
    cN
    @18
    cM
    nbusgrf1o1.n
    eleq2i
    @2
    @19
    @17
    @19
    @17
    wb
    @2
    cG
    cU
    cM
    nbgrsym
    a1i
    biimpd
    syl5bi
    imp
    vi
    cE
    cG
    cU
    cM
    nbusgrf1o1.e
    nbusgredgeu
    syl2anc
    @10
    vi
    cE
    df-reu
    sylib
    @4
    @11
    @14
    vi
    @11
    @6
    @7
    @10
    wa
    #
    wa
    @4
    @14
    @6
    @7
    @10
    anass
    @4
    @20
    @10
    @6
    @4
    @10
    @20
    @4
    @10
    @7
    @4
    @7
    @10
    cU
    @9
    wcel
    #
    @1
    @21
    @0
    @3
    cU
    cM
    cV
    prid1g
    ad2antlr
    @5
    @9
    cU
    eleq2
    syl5ibrcom
    pm4.71rd
    bicomd
    anbi2d
    syl5bb
    eubidv
    mpbird
    @13
    @5
    cI
    wcel
    #
    @10
    wa
    #
    vi
    weu
    @12
    @10
    vi
    cI
    df-reu
    @23
    @11
    vi
    @22
    @8
    @10
    cU
    ve
    cv
    #
    wcel
    @7
    ve
    @5
    cE
    cI
    @24
    @5
    cU
    eleq2
    nbusgrf1o1.i
    elrab2
    anbi1i
    eubii
    bitri
    sylibr
end
