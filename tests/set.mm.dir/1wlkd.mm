include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cdm.mm"
include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "cfzo.mm"
include "wral.mm"
include "1wlkdlem3.mm"
include "1wlkdlem1.mm"
include "1wlkdlem4.mm"
include "cvv.mm"
include "w3a.mm"
include "wb.mm"
include "1vgrex.mm"
include "iswlkg.mm"
include "3syl.mm"
include "mpbir3and.mm"

theorem 1wlkd
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


  assert |- ( ph -> F ( Walks ` G ) P )

  proof
    wph
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cF
    cI
    cdm
    cword
    wcel
    #
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    cV
    cP
    wf
    #
    vk
    cv
    #
    cP
    cfv
    #
    @4
    c1
    caddc
    co
    cP
    cfv
    #
    wceq
    @4
    cF
    cfv
    cI
    cfv
    #
    @5
    csn
    wceq
    @5
    @6
    cpr
    @7
    wss
    wif
    vk
    cc0
    @2
    cfzo
    co
    wral
    #
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
    1wlkdlem3
    wph
    cP
    cF
    cJ
    cV
    cX
    cY
    1wlkd.p
    1wlkd.f
    1wlkd.x
    1wlkd.y
    1wlkdlem1
    wph
    cP
    vk
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
    1wlkdlem4
    wph
    cX
    cV
    wcel
    cG
    cvv
    wcel
    @0
    @1
    @3
    @8
    w3a
    wb
    1wlkd.x
    cG
    cX
    cV
    1wlkd.v
    1vgrex
    cP
    vk
    cF
    cG
    cI
    cV
    cvv
    1wlkd.v
    1wlkd.i
    iswlkg
    3syl
    mpbir3and
end
