include "cz.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "cres.mm"
include "id.mm"
include "cv.mm"
include "wceq.mm"
include "fvres.mm"
include "adantl.mm"
include "seqfeq.mm"

theorem seqres
  let c.pl: class .+
  let cF: class F
  let cM: class M
  let vk: setvar k


  assert |- ( M e. ZZ -> seq M ( .+ , ( F |` ( ZZ>= ` M ) ) ) = seq M ( .+ , F ) )

  proof
    cM
    cz
    wcel
    #
    c.pl
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
    @0
    id
    vk
    cv
    #
    @1
    wcel
    @3
    @2
    cfv
    @3
    cF
    cfv
    wceq
    @0
    @3
    @1
    cF
    fvres
    adantl
    seqfeq
end
