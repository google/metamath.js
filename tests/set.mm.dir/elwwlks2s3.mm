include "c2.mm"
include "cwwlksn.mm"
include "co.mm"
include "wcel.mm"
include "cn0.mm"
include "cvtx.mm"
include "cfv.mm"
include "cword.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "cs3.mm"
include "wrex.mm"
include "wwlknbp1.mm"
include "c3.mm"
include "wa.mm"
include "wrdeqi.mm"
include "eleq2i.mm"
include "df-3.mm"
include "eqeq2i.mm"
include "anbi12i.mm"
include "wrdl3s3.mm"
include "sylbb1.mm"
include "3adant1.mm"
include "syl.mm"

theorem elwwlks2s3
  let cG: class G
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume elwwlks2s3.v: |- V = ( Vtx ` G )

  disjoint V a
  disjoint V b
  disjoint V c
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint W a
  disjoint W b
  disjoint W c
  assert |- ( W e. ( 2 WWalksN G ) -> E. a e. V E. b e. V E. c e. V W = <" a b c "> )

  proof
    cW
    c2
    cG
    cwwlksn
    co
    wcel
    c2
    cn0
    wcel
    #
    cW
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    cW
    chash
    cfv
    #
    c2
    c1
    caddc
    co
    #
    wceq
    #
    w3a
    cW
    va
    cv
    vb
    cv
    vc
    cv
    cs3
    wceq
    vc
    cV
    wrex
    vb
    cV
    wrex
    va
    cV
    wrex
    #
    cG
    c2
    cW
    wwlknbp1
    @3
    @6
    @7
    @0
    cW
    cV
    cword
    #
    wcel
    #
    @4
    c3
    wceq
    #
    wa
    @3
    @6
    wa
    @7
    @9
    @3
    @10
    @6
    @8
    @2
    cW
    cV
    @1
    elwwlks2s3.v
    wrdeqi
    eleq2i
    c3
    @5
    @4
    df-3
    eqeq2i
    anbi12i
    cV
    cW
    va
    vb
    vc
    wrdl3s3
    sylbb1
    3adant1
    syl
end
