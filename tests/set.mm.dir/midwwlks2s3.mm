include "c2.mm"
include "cwwlksn.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cs3.mm"
include "wceq.mm"
include "wrex.mm"
include "c1.mm"
include "cfv.mm"
include "elwwlks2s3.mm"
include "wa.mm"
include "wi.mm"
include "fveq1.mm"
include "s3fv1.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "adantl.mm"
include "rexlimdvw.mm"
include "reximdva.mm"
include "rexlimiv.mm"
include "syl.mm"

theorem midwwlks2s3
  let cG: class G
  let cV: class V
  let cW: class W
  let vb: setvar b
  let va: setvar a
  let vc: setvar c
  assume elwwlks2s3.v: |- V = ( Vtx ` G )

  disjoint V b
  disjoint W b
  disjoint V a
  disjoint V c
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint W a
  disjoint W c
  assert |- ( W e. ( 2 WWalksN G ) -> E. b e. V ( W ` 1 ) = b )

  proof
    cW
    c2
    cG
    cwwlksn
    co
    wcel
    cW
    va
    cv
    #
    vb
    cv
    #
    vc
    cv
    #
    cs3
    #
    wceq
    #
    vc
    cV
    wrex
    #
    vb
    cV
    wrex
    #
    va
    cV
    wrex
    c1
    cW
    cfv
    #
    @1
    wceq
    #
    vb
    cV
    wrex
    #
    cG
    cV
    cW
    va
    vb
    vc
    elwwlks2s3.v
    elwwlks2s3
    @6
    @9
    va
    cV
    @0
    cV
    wcel
    #
    @5
    @8
    vb
    cV
    @10
    @1
    cV
    wcel
    #
    wa
    @4
    @8
    vc
    cV
    @11
    @4
    @8
    wi
    @10
    @11
    @4
    @8
    @4
    @11
    @7
    c1
    @3
    cfv
    @1
    c1
    cW
    @3
    fveq1
    @0
    @1
    @2
    cV
    s3fv1
    sylan9eqr
    ex
    adantl
    rexlimdvw
    reximdva
    rexlimiv
    syl
end
