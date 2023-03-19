include "cfv.mm"
include "wcel.mm"
include "cdm.mm"
include "cword.mm"
include "1wlkdlem2.mm"
include "elfvdm.mm"
include "cs1.mm"
include "s1cl.mm"
include "syl5eqel.mm"
include "3syl.mm"

theorem 1wlkdlem3
  let wph: wff ph
  let cP: class P
  let cF: class F
  let cI: class I
  let cJ: class J
  let cV: class V
  let cX: class X
  let cY: class Y
  assume 1wlkd.p: |- P = <" X Y ">
  assume 1wlkd.f: |- F = <" J ">
  assume 1wlkd.x: |- ( ph -> X e. V )
  assume 1wlkd.y: |- ( ph -> Y e. V )
  assume 1wlkd.l: |- ( ( ph /\ X = Y ) -> ( I ` J ) = { X } )
  assume 1wlkd.j: |- ( ( ph /\ X =/= Y ) -> { X , Y } C_ ( I ` J ) )


  assert |- ( ph -> F e. Word dom I )

  proof
    wph
    cX
    cJ
    cI
    cfv
    wcel
    cJ
    cI
    cdm
    #
    wcel
    #
    cF
    @0
    cword
    #
    wcel
    wph
    cP
    cF
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
    1wlkdlem2
    cX
    cJ
    cI
    elfvdm
    @1
    cF
    cJ
    cs1
    @2
    1wlkd.f
    cJ
    @0
    s1cl
    syl5eqel
    3syl
end
