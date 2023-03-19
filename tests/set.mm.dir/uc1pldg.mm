include "wcel.mm"
include "cpl1.mm"
include "cfv.mm"
include "cbs.mm"
include "c0g.mm"
include "wne.mm"
include "cco1.mm"
include "eqid.mm"
include "isuc1p.mm"
include "simp3bi.mm"

theorem uc1pldg
  let cC: class C
  let cD: class D
  let cR: class R
  let cU: class U
  let cF: class F
  assume uc1pldg.d: |- D = ( deg1 ` R )
  assume uc1pldg.u: |- U = ( Unit ` R )
  assume uc1pldg.c: |- C = ( Unic1p ` R )


  assert |- ( F e. C -> ( ( coe1 ` F ) ` ( D ` F ) ) e. U )

  proof
    cF
    cC
    wcel
    cF
    cR
    cpl1
    cfv
    #
    cbs
    cfv
    #
    wcel
    cF
    @0
    c0g
    cfv
    #
    wne
    cF
    cD
    cfv
    cF
    cco1
    cfv
    cfv
    cU
    wcel
    @1
    cC
    cD
    @0
    cR
    cU
    cF
    @2
    @0
    eqid
    @1
    eqid
    @2
    eqid
    uc1pldg.d
    uc1pldg.c
    uc1pldg.u
    isuc1p
    simp3bi
end
