include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cmap.mm"
include "cv.mm"
include "cword.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cab.mm"
include "crab.mm"
include "wf.mm"
include "cvv.mm"
include "wb.mm"
include "ovexd.mm"
include "elmapg.mm"
include "syldan.mm"
include "iswrdi.mm"
include "adantl.mm"
include "fnfzo0hash.mm"
include "adantll.mm"
include "jca.mm"
include "ex.mm"
include "wrdf.mm"
include "oveq2.mm"
include "feq2d.mm"
include "syl5ibcom.mm"
include "imp.mm"
include "impbid1.mm"
include "bitrd.mm"
include "abbi2dv.mm"
include "df-rab.mm"
include "syl6reqr.mm"

theorem wrdnval
  let vw: setvar w
  let cN: class N
  let cV: class V
  let cX: class X
  let cW: class W

  disjoint N w
  disjoint V w
  disjoint X w
  disjoint W w
  assert |- ( ( V e. X /\ N e. NN0 ) -> { w e. Word V | ( # ` w ) = N } = ( V ^m ( 0 ..^ N ) ) )

  proof
    cV
    cX
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cV
    cc0
    cN
    cfzo
    co
    #
    cmap
    co
    #
    vw
    cv
    #
    cV
    cword
    #
    wcel
    #
    @5
    chash
    cfv
    #
    cN
    wceq
    #
    wa
    #
    vw
    cab
    @9
    vw
    @6
    crab
    @2
    @10
    vw
    @4
    @2
    @5
    @4
    wcel
    #
    @3
    cV
    @5
    wf
    #
    @10
    @0
    @1
    @3
    cvv
    wcel
    @11
    @12
    wb
    @2
    cc0
    cN
    cfzo
    ovexd
    cV
    @3
    @5
    cX
    cvv
    elmapg
    syldan
    @2
    @12
    @10
    @2
    @12
    @10
    @2
    @12
    wa
    @7
    @9
    @12
    @7
    @2
    cV
    cN
    @5
    iswrdi
    adantl
    @1
    @12
    @9
    @0
    cV
    @5
    cN
    fnfzo0hash
    adantll
    jca
    ex
    @7
    @9
    @12
    @7
    cc0
    @8
    cfzo
    co
    #
    cV
    @5
    wf
    @9
    @12
    cV
    @5
    wrdf
    @9
    @13
    @3
    cV
    @5
    @8
    cN
    cc0
    cfzo
    oveq2
    feq2d
    syl5ibcom
    imp
    impbid1
    bitrd
    abbi2dv
    @9
    vw
    @6
    df-rab
    syl6reqr
end
