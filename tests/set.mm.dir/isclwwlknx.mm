include "cn.mm"
include "wcel.mm"
include "cword.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "cc0.mm"
include "chash.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "clsw.mm"
include "wa.mm"
include "wceq.mm"
include "cclwwlkn.mm"
include "w3a.mm"
include "wb.mm"
include "wi.mm"
include "eleq1.mm"
include "len0nnbi.mm"
include "biimprcd.mm"
include "syl6bir.mm"
include "impcom.mm"
include "imp.mm"
include "biantrurd.mm"
include "bicomd.mm"
include "pm5.32da.mm"
include "ex.mm"
include "pm5.32rd.mm"
include "cclwwlk.mm"
include "isclwwlkn.mm"
include "isclwwlk.mm"
include "3anass.mm"
include "anass.mm"
include "bitri.mm"
include "anbi1i.mm"
include "3bitr4g.mm"

theorem isclwwlknx
  let vi: setvar i
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  assume isclwwlknx.v: |- V = ( Vtx ` G )
  assume isclwwlknx.e: |- E = ( Edg ` G )

  disjoint G i
  disjoint W i
  assert |- ( N e. NN -> ( W e. ( N ClWWalksN G ) <-> ( ( W e. Word V /\ A. i e. ( 0 ..^ ( ( # ` W ) - 1 ) ) { ( W ` i ) , ( W ` ( i + 1 ) ) } e. E /\ { ( lastS ` W ) , ( W ` 0 ) } e. E ) /\ ( # ` W ) = N ) ) )

  proof
    cN
    cn
    wcel
    #
    cW
    cV
    cword
    wcel
    #
    cW
    c0
    wne
    #
    vi
    cv
    #
    cW
    cfv
    @3
    c1
    caddc
    co
    cW
    cfv
    cpr
    cE
    wcel
    vi
    cc0
    cW
    chash
    cfv
    #
    c1
    cmin
    co
    cfzo
    co
    wral
    #
    cW
    clsw
    cfv
    cc0
    cW
    cfv
    cpr
    cE
    wcel
    #
    wa
    #
    wa
    #
    wa
    #
    @4
    cN
    wceq
    #
    wa
    #
    @1
    @7
    wa
    #
    @10
    wa
    cW
    cN
    cG
    cclwwlkn
    co
    wcel
    #
    @1
    @5
    @6
    w3a
    #
    @10
    wa
    @0
    @10
    @9
    @12
    @0
    @10
    @9
    @12
    wb
    @0
    @10
    wa
    #
    @1
    @8
    @7
    @15
    @1
    wa
    #
    @7
    @8
    @16
    @2
    @7
    @15
    @1
    @2
    @10
    @0
    @1
    @2
    wi
    #
    @10
    @0
    @4
    cn
    wcel
    #
    @17
    @4
    cN
    cn
    eleq1
    @1
    @2
    @18
    cV
    cW
    len0nnbi
    biimprcd
    syl6bir
    impcom
    imp
    biantrurd
    bicomd
    pm5.32da
    ex
    pm5.32rd
    @13
    cW
    cG
    cclwwlk
    cfv
    wcel
    #
    @10
    wa
    @11
    cG
    cN
    cW
    isclwwlkn
    @19
    @9
    @10
    @19
    @1
    @2
    wa
    #
    @5
    @6
    w3a
    #
    @9
    vi
    cE
    cG
    cV
    cW
    isclwwlknx.v
    isclwwlknx.e
    isclwwlk
    @21
    @20
    @7
    wa
    @9
    @20
    @5
    @6
    3anass
    @1
    @2
    @7
    anass
    bitri
    bitri
    anbi1i
    bitri
    @14
    @12
    @10
    @1
    @5
    @6
    3anass
    anbi1i
    3bitr4g
end
