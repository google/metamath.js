include "cv.mm"
include "co.mm"
include "wbr.mm"
include "cif.mm"
include "csb.mm"
include "biid.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "vex.mm"
include "cdleme31sc.mm"
include "ax-mp.mm"
include "ifbieq2i.mm"
include "eqtr4i.mm"

theorem cdleme31sdnN
  let vt: setvar t
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cU: class U
  let cI: class I
  let c.or: class .\/
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let vs: setvar s
  assume cdleme31sdn.c: |- C = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdleme31sdn.d: |- D = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdleme31sdn.n: |- N = if ( s .<_ ( P .\/ Q ) , I , C )

  disjoint .\/ t
  disjoint ./\ t
  disjoint P t
  disjoint Q t
  disjoint U t
  disjoint W t
  disjoint s t
  assert |- N = if ( s .<_ ( P .\/ Q ) , I , [_ s / t ]_ D )

  proof
    cN
    vs
    cv
    #
    cP
    cQ
    c.or
    co
    c.le
    wbr
    #
    cI
    cC
    cif
    @1
    cI
    vt
    @0
    cD
    csb
    #
    cif
    cdleme31sdn.n
    @1
    @1
    @2
    cC
    cI
    @1
    biid
    @0
    cvv
    wcel
    @2
    cC
    wceq
    vs
    vex
    cvv
    cD
    cP
    cQ
    @0
    cU
    c.or
    c.an
    cW
    cC
    vt
    cdleme31sdn.d
    cdleme31sdn.c
    cdleme31sc
    ax-mp
    ifbieq2i
    eqtr4i
end
