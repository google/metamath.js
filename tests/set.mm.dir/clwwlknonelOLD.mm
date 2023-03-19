include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cclwwlknon.mm"
include "cfv.mm"
include "co.mm"
include "cclwwlkn.mm"
include "cc0.mm"
include "wceq.mm"
include "cword.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "chash.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "clsw.mm"
include "w3a.mm"
include "cn0.mm"
include "wb.mm"
include "nnnn0.mm"
include "isclwwlknonOLD.mm"
include "sylan2.mm"
include "isclwwlknx.mm"
include "adantl.mm"
include "anbi1d.mm"
include "df-3an.mm"
include "syl6bbr.mm"
include "bitrd.mm"

theorem clwwlknonelOLD
  let vi: setvar i
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume clwwlknonel.v: |- V = ( Vtx ` G )
  assume clwwlknonel.e: |- E = ( Edg ` G )

  disjoint G i
  disjoint W i
  assert |- ( ( X e. V /\ N e. NN ) -> ( W e. ( X ( ClWWalksNOn ` G ) N ) <-> ( ( W e. Word V /\ A. i e. ( 0 ..^ ( ( # ` W ) - 1 ) ) { ( W ` i ) , ( W ` ( i + 1 ) ) } e. E /\ { ( lastS ` W ) , ( W ` 0 ) } e. E ) /\ ( # ` W ) = N /\ ( W ` 0 ) = X ) ) )

  proof
    cX
    cV
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cW
    cX
    cN
    cG
    cclwwlknon
    cfv
    co
    wcel
    #
    cW
    cN
    cG
    cclwwlkn
    co
    wcel
    #
    cc0
    cW
    cfv
    #
    cX
    wceq
    #
    wa
    #
    cW
    cV
    cword
    wcel
    vi
    cv
    #
    cW
    cfv
    @8
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
    cW
    clsw
    cfv
    @5
    cpr
    cE
    wcel
    w3a
    #
    @9
    cN
    wceq
    #
    @6
    w3a
    #
    @1
    @0
    cN
    cn0
    wcel
    @3
    @7
    wb
    cN
    nnnn0
    cG
    cN
    cV
    cW
    cX
    clwwlknonel.v
    isclwwlknonOLD
    sylan2
    @2
    @7
    @10
    @11
    wa
    #
    @6
    wa
    @12
    @2
    @4
    @13
    @6
    @1
    @4
    @13
    wb
    @0
    vi
    cE
    cG
    cN
    cV
    cW
    clwwlknonel.v
    clwwlknonel.e
    isclwwlknx
    adantl
    anbi1d
    @10
    @11
    @6
    df-3an
    syl6bbr
    bitrd
end
