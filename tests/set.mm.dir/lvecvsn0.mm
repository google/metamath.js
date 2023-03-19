include "co.mm"
include "wne.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "lvecvs0or.mm"
include "necon3abid.mm"
include "neanior.mm"
include "syl6bbr.mm"

theorem lvecvsn0
  let wph: wff ph
  let cA: class A
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lvecmul0or.v: |- V = ( Base ` W )
  assume lvecmul0or.s: |- .x. = ( .s ` W )
  assume lvecmul0or.f: |- F = ( Scalar ` W )
  assume lvecmul0or.k: |- K = ( Base ` F )
  assume lvecmul0or.o: |- O = ( 0g ` F )
  assume lvecmul0or.z: |- .0. = ( 0g ` W )
  assume lvecmul0or.w: |- ( ph -> W e. LVec )
  assume lvecmul0or.a: |- ( ph -> A e. K )
  assume lvecmul0or.x: |- ( ph -> X e. V )


  assert |- ( ph -> ( ( A .x. X ) =/= .0. <-> ( A =/= O /\ X =/= .0. ) ) )

  proof
    wph
    cA
    cX
    c.x
    co
    #
    c.0
    wne
    cA
    cO
    wceq
    cX
    c.0
    wceq
    wo
    #
    wn
    cA
    cO
    wne
    cX
    c.0
    wne
    wa
    wph
    @1
    @0
    c.0
    wph
    cA
    c.x
    cF
    cK
    cO
    cV
    cW
    cX
    c.0
    lvecmul0or.v
    lvecmul0or.s
    lvecmul0or.f
    lvecmul0or.k
    lvecmul0or.o
    lvecmul0or.z
    lvecmul0or.w
    lvecmul0or.a
    lvecmul0or.x
    lvecvs0or
    necon3abid
    cA
    cO
    cX
    c.0
    neanior
    syl6bbr
end
