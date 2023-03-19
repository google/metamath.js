include "csetrecs.mm"
include "c0.mm"
include "wss.mm"
include "wceq.mm"
include "eqid.mm"
include "cv.mm"
include "cfv.mm"
include "wi.mm"
include "ss0.mm"
include "fveq2.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "eqimss.mm"
include "syl56.mm"
include "alrimiv.mm"
include "setrec2v.mm"
include "syl.mm"

theorem 0setrec
  let wph: wff ph
  let cF: class F
  let vx: setvar x
  let vk: setvar k
  assume 0setrec.1: |- ( ph -> ( F ` (/) ) = (/) )


  assert |- ( ph -> setrecs ( F ) = (/) )

  proof
    wph
    cF
    csetrecs
    #
    c0
    wss
    @0
    c0
    wceq
    wph
    @0
    c0
    cF
    vx
    @0
    eqid
    wph
    vx
    cv
    #
    c0
    wss
    #
    @1
    cF
    cfv
    #
    c0
    wss
    #
    wi
    vx
    @2
    @1
    c0
    wceq
    #
    wph
    @3
    c0
    wceq
    #
    @4
    @1
    ss0
    wph
    @5
    @6
    @5
    wph
    @3
    c0
    cF
    cfv
    c0
    @1
    c0
    cF
    fveq2
    0setrec.1
    sylan9eqr
    ex
    @3
    c0
    eqimss
    syl56
    alrimiv
    setrec2v
    @0
    ss0
    syl
end
