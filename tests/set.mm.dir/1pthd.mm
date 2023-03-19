include "ctrls.mm"
include "cfv.mm"
include "wbr.mm"
include "cpths.mm"
include "1trld.mm"
include "wa.mm"
include "c1.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "cres.mm"
include "ccnv.mm"
include "wfun.mm"
include "cc0.mm"
include "cpr.mm"
include "cima.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "simpr.mm"
include "1pthdlem1.mm"
include "a1i.mm"
include "1pthdlem2.mm"
include "ispth.mm"
include "syl3anbrc.mm"
include "mpdan.mm"

theorem 1pthd
  let wph: wff ph
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  let cV: class V
  let cX: class X
  let cY: class Y
  let vk: setvar k
  assume 1wlkd.p: |- P = <" X Y ">
  assume 1wlkd.f: |- F = <" J ">
  assume 1wlkd.x: |- ( ph -> X e. V )
  assume 1wlkd.y: |- ( ph -> Y e. V )
  assume 1wlkd.l: |- ( ( ph /\ X = Y ) -> ( I ` J ) = { X } )
  assume 1wlkd.j: |- ( ( ph /\ X =/= Y ) -> { X , Y } C_ ( I ` J ) )
  assume 1wlkd.v: |- V = ( Vtx ` G )
  assume 1wlkd.i: |- I = ( iEdg ` G )


  assert |- ( ph -> F ( Paths ` G ) P )

  proof
    wph
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    cF
    cP
    cG
    cpths
    cfv
    wbr
    #
    wph
    cP
    cF
    cG
    cI
    cJ
    cV
    cX
    cY
    1wlkd.p
    1wlkd.f
    1wlkd.x
    1wlkd.y
    1wlkd.l
    1wlkd.j
    1wlkd.v
    1wlkd.i
    1trld
    wph
    @0
    wa
    #
    @0
    cP
    c1
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    cres
    ccnv
    wfun
    #
    cP
    cc0
    @3
    cpr
    cima
    cP
    @4
    cima
    cin
    c0
    wceq
    #
    @1
    wph
    @0
    simpr
    @5
    @2
    cP
    cF
    cJ
    cX
    cY
    1wlkd.p
    1wlkd.f
    1pthdlem1
    a1i
    @6
    @2
    cP
    cF
    cJ
    cX
    cY
    1wlkd.p
    1wlkd.f
    1pthdlem2
    a1i
    cP
    cF
    cG
    ispth
    syl3anbrc
    mpdan
end
