include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wne.mm"
include "cdg1.mm"
include "cco1.mm"
include "cur.mm"
include "wceq.mm"
include "eqid.mm"
include "ismon1p.mm"
include "simp2bi.mm"

theorem mon1pn0
  let cP: class P
  let cR: class R
  let cF: class F
  let cM: class M
  let c.0: class .0.
  assume uc1pn0.p: |- P = ( Poly1 ` R )
  assume uc1pn0.z: |- .0. = ( 0g ` P )
  assume mon1pn0.m: |- M = ( Monic1p ` R )


  assert |- ( F e. M -> F =/= .0. )

  proof
    cF
    cM
    wcel
    cF
    cP
    cbs
    cfv
    #
    wcel
    cF
    c.0
    wne
    cF
    cR
    cdg1
    cfv
    #
    cfv
    cF
    cco1
    cfv
    cfv
    cR
    cur
    cfv
    #
    wceq
    @0
    @1
    cP
    cR
    @2
    cF
    cM
    c.0
    uc1pn0.p
    @0
    eqid
    uc1pn0.z
    @1
    eqid
    mon1pn0.m
    @2
    eqid
    ismon1p
    simp2bi
end
