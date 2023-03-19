include "cen.mm"
include "wbr.mm"
include "cpw.mm"
include "c2o.mm"
include "cmap.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "relen.mm"
include "brrelexi.mm"
include "pw2eng.mm"
include "syl.mm"
include "com.mm"
include "2onn.mm"
include "elexi.mm"
include "enref.mm"
include "mapen.mm"
include "mpan.mm"
include "brrelex2i.mm"
include "ensym.mm"
include "3syl.mm"
include "entr.mm"
include "syl2anc.mm"

theorem pwen
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cV: class V
  let cW: class W


  assert |- ( A ~~ B -> ~P A ~~ ~P B )

  proof
    cA
    cB
    cen
    wbr
    #
    cA
    cpw
    #
    c2o
    cA
    cmap
    co
    #
    cen
    wbr
    #
    @2
    cB
    cpw
    #
    cen
    wbr
    #
    @1
    @4
    cen
    wbr
    @0
    cA
    cvv
    wcel
    @3
    cA
    cB
    cen
    relen
    brrelexi
    cA
    cvv
    pw2eng
    syl
    @0
    @2
    c2o
    cB
    cmap
    co
    #
    cen
    wbr
    #
    @6
    @4
    cen
    wbr
    #
    @5
    c2o
    c2o
    cen
    wbr
    @0
    @7
    c2o
    c2o
    com
    2onn
    elexi
    enref
    c2o
    c2o
    cA
    cB
    mapen
    mpan
    @0
    cB
    cvv
    wcel
    @4
    @6
    cen
    wbr
    @8
    cA
    cB
    cen
    relen
    brrelex2i
    cB
    cvv
    pw2eng
    @4
    @6
    ensym
    3syl
    @2
    @6
    @4
    entr
    syl2anc
    @1
    @2
    @4
    entr
    syl2anc
end
