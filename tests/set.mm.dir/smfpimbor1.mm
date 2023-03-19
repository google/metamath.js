include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "crest.mm"
include "co.mm"
include "wcel.mm"
include "cr.mm"
include "cpw.mm"
include "crab.mm"
include "eqid.mm"
include "smfpimbor1lem2.mm"

theorem smfpimbor1
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cP: class P
  let cS: class S
  let cE: class E
  let cF: class F
  let cJ: class J
  let ve: setvar e
  let vk: setvar k
  let vx: setvar x
  assume smfpimbor1.s: |- ( ph -> S e. SAlg )
  assume smfpimbor1.f: |- ( ph -> F e. ( SMblFn ` S ) )
  assume smfpimbor1.a: |- D = dom F
  assume smfpimbor1.j: |- J = ( topGen ` ran (,) )
  assume smfpimbor1.b: |- B = ( SalGen ` J )
  assume smfpimbor1.e: |- ( ph -> E e. B )
  assume smfpimbor1.p: |- P = ( `' F " E )


  assert |- ( ph -> P e. ( S |`t D ) )

  proof
    wph
    cB
    cD
    cP
    cS
    cF
    ccnv
    ve
    cv
    cima
    cS
    cD
    crest
    co
    wcel
    ve
    cr
    cpw
    crab
    #
    ve
    cE
    cF
    cJ
    smfpimbor1.s
    smfpimbor1.f
    smfpimbor1.a
    smfpimbor1.j
    smfpimbor1.b
    smfpimbor1.e
    smfpimbor1.p
    @0
    eqid
    smfpimbor1lem2
end
