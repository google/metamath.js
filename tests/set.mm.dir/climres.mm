include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cuz.mm"
include "cfv.mm"
include "cres.mm"
include "cvv.mm"
include "eqid.mm"
include "resexg.mm"
include "adantl.mm"
include "simpr.mm"
include "simpl.mm"
include "cv.mm"
include "wceq.mm"
include "fvres.mm"
include "climeq.mm"

theorem climres
  let cA: class A
  let cF: class F
  let cM: class M
  let cV: class V
  let vf: setvar f
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x


  assert |- ( ( M e. ZZ /\ F e. V ) -> ( ( F |` ( ZZ>= ` M ) ) ~~> A <-> F ~~> A ) )

  proof
    cM
    cz
    wcel
    #
    cF
    cV
    wcel
    #
    wa
    #
    cA
    vk
    cF
    cM
    cuz
    cfv
    #
    cres
    #
    cF
    cM
    cvv
    cV
    @3
    @3
    eqid
    @1
    @4
    cvv
    wcel
    @0
    cF
    @3
    cV
    resexg
    adantl
    @0
    @1
    simpr
    @0
    @1
    simpl
    vk
    cv
    #
    @3
    wcel
    @5
    @4
    cfv
    @5
    cF
    cfv
    wceq
    @2
    @5
    @3
    cF
    fvres
    adantl
    climeq
end
