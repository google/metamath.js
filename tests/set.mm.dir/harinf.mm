include "wcel.mm"
include "cfn.mm"
include "wn.mm"
include "wa.mm"
include "com.mm"
include "char.mm"
include "cfv.mm"
include "cv.mm"
include "con0.mm"
include "cdom.mm"
include "wbr.mm"
include "nnon.mm"
include "adantl.mm"
include "csdm.mm"
include "simplr.mm"
include "nnfi.mm"
include "sdomdom.mm"
include "domfi.mm"
include "ex.mm"
include "syl2im.mm"
include "mtod.mm"
include "wb.mm"
include "simpll.mm"
include "fidomtri.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "elharval.mm"
include "sylanbrc.mm"
include "ssrdv.mm"

theorem harinf
  let cS: class S
  let cV: class V
  let vx: setvar x


  assert |- ( ( S e. V /\ -. S e. Fin ) -> _om C_ ( har ` S ) )

  proof
    cS
    cV
    wcel
    #
    cS
    cfn
    wcel
    #
    wn
    #
    wa
    #
    vx
    com
    cS
    char
    cfv
    #
    @3
    vx
    cv
    #
    com
    wcel
    #
    @5
    @4
    wcel
    #
    @3
    @6
    wa
    #
    @5
    con0
    wcel
    #
    @5
    cS
    cdom
    wbr
    #
    @7
    @6
    @9
    @3
    @5
    nnon
    adantl
    @8
    @10
    cS
    @5
    csdm
    wbr
    #
    wn
    #
    @8
    @11
    @1
    @0
    @2
    @6
    simplr
    @8
    @5
    cfn
    wcel
    #
    @11
    cS
    @5
    cdom
    wbr
    #
    @1
    @6
    @13
    @3
    @5
    nnfi
    adantl
    #
    cS
    @5
    sdomdom
    @13
    @14
    @1
    @5
    cS
    domfi
    ex
    syl2im
    mtod
    @8
    @13
    @0
    @10
    @12
    wb
    @15
    @0
    @2
    @6
    simpll
    @5
    cS
    cV
    fidomtri
    syl2anc
    mpbird
    cS
    @5
    elharval
    sylanbrc
    ex
    ssrdv
end
