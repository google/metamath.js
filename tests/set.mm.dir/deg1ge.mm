include "wcel.mm"
include "cn0.mm"
include "cfv.mm"
include "wne.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wn.mm"
include "clt.mm"
include "wceq.mm"
include "cxr.mm"
include "wb.mm"
include "deg1xrcl.mm"
include "nn0re.mm"
include "rexrd.mm"
include "xrltnle.mm"
include "syl2an.mm"
include "deg1lt.mm"
include "3expia.mm"
include "sylbird.mm"
include "necon1ad.mm"
include "3impia.mm"

theorem deg1ge
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cF: class F
  let cG: class G
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let vb: setvar b
  let va: setvar a
  assume deg1leb.d: |- D = ( deg1 ` R )
  assume deg1leb.p: |- P = ( Poly1 ` R )
  assume deg1leb.b: |- B = ( Base ` P )
  assume deg1leb.y: |- .0. = ( 0g ` R )
  assume deg1leb.a: |- A = ( coe1 ` F )


  assert |- ( ( F e. B /\ G e. NN0 /\ ( A ` G ) =/= .0. ) -> G <_ ( D ` F ) )

  proof
    cF
    cB
    wcel
    #
    cG
    cn0
    wcel
    #
    cG
    cA
    cfv
    #
    c.0
    wne
    cG
    cF
    cD
    cfv
    #
    cle
    wbr
    #
    @0
    @1
    wa
    #
    @4
    @2
    c.0
    @5
    @4
    wn
    #
    @3
    cG
    clt
    wbr
    #
    @2
    c.0
    wceq
    #
    @0
    @3
    cxr
    wcel
    cG
    cxr
    wcel
    @7
    @6
    wb
    @1
    cB
    cD
    cP
    cR
    cF
    deg1leb.d
    deg1leb.p
    deg1leb.b
    deg1xrcl
    @1
    cG
    cG
    nn0re
    rexrd
    @3
    cG
    xrltnle
    syl2an
    @0
    @1
    @7
    @8
    cA
    cB
    cD
    cP
    cR
    cF
    cG
    c.0
    deg1leb.d
    deg1leb.p
    deg1leb.b
    deg1leb.y
    deg1leb.a
    deg1lt
    3expia
    sylbird
    necon1ad
    3impia
end
