include "cres.mm"
include "wceq.mm"
include "cdm.mm"
include "id.mm"
include "dmeq.mm"
include "reseq2d.mm"
include "resdmres.mm"
include "syl6req.mm"
include "eqtrd.mm"

theorem resresdm
  let cA: class A
  let cE: class E
  let cF: class F


  assert |- ( F = ( E |` A ) -> F = ( E |` dom F ) )

  proof
    cF
    cE
    cA
    cres
    #
    wceq
    #
    cF
    @0
    cE
    cF
    cdm
    #
    cres
    #
    @1
    id
    @1
    @3
    cE
    @0
    cdm
    #
    cres
    @0
    @1
    @2
    @4
    cE
    cF
    @0
    dmeq
    reseq2d
    cE
    cA
    resdmres
    syl6req
    eqtrd
end
