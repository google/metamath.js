include "ciedg.mm"
include "cfv.mm"
include "cvtx.mm"
include "upgr1wlkdlem1.mm"
include "upgr1wlkdlem2.mm"
include "eqid.mm"
include "1pthond.mm"

theorem upgr1pthond
  let wph: wff ph
  let cP: class P
  let cF: class F
  let cG: class G
  let cJ: class J
  let cX: class X
  let cY: class Y
  assume upgr1wlkd.p: |- P = <" X Y ">
  assume upgr1wlkd.f: |- F = <" J ">
  assume upgr1wlkd.x: |- ( ph -> X e. ( Vtx ` G ) )
  assume upgr1wlkd.y: |- ( ph -> Y e. ( Vtx ` G ) )
  assume upgr1wlkd.j: |- ( ph -> ( ( iEdg ` G ) ` J ) = { X , Y } )
  assume upgr1wlkd.g: |- ( ph -> G e. UPGraph )


  assert |- ( ph -> F ( X ( PathsOn ` G ) Y ) P )

  proof
    wph
    cP
    cF
    cG
    cG
    ciedg
    cfv
    #
    cJ
    cG
    cvtx
    cfv
    #
    cX
    cY
    upgr1wlkd.p
    upgr1wlkd.f
    upgr1wlkd.x
    upgr1wlkd.y
    wph
    cP
    cF
    cG
    cJ
    cX
    cY
    upgr1wlkd.p
    upgr1wlkd.f
    upgr1wlkd.x
    upgr1wlkd.y
    upgr1wlkd.j
    upgr1wlkdlem1
    wph
    cP
    cF
    cG
    cJ
    cX
    cY
    upgr1wlkd.p
    upgr1wlkd.f
    upgr1wlkd.x
    upgr1wlkd.y
    upgr1wlkd.j
    upgr1wlkdlem2
    @1
    eqid
    @0
    eqid
    1pthond
end
