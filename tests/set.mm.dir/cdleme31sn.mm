include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wbr.mm"
include "cif.mm"
include "csb.mm"
include "wnfc.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfif.mm"
include "a1i.mm"
include "wceq.mm"
include "breq1.mm"
include "csbeq1a.mm"
include "ifbieq12d.mm"
include "csbiegf.mm"
include "csbeq2i.mm"
include "3eqtr4g.mm"

theorem cdleme31sn
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cI: class I
  let c.or: class .\/
  let c.le: class .<_
  let cN: class N
  let vs: setvar s
  assume cdleme31sn.n: |- N = if ( s .<_ ( P .\/ Q ) , I , D )
  assume cdleme31sn.c: |- C = if ( R .<_ ( P .\/ Q ) , [_ R / s ]_ I , [_ R / s ]_ D )

  disjoint A s
  disjoint .\/ s
  disjoint .<_ s
  disjoint P s
  disjoint Q s
  disjoint R s
  assert |- ( R e. A -> [_ R / s ]_ N = C )

  proof
    cR
    cA
    wcel
    #
    vs
    cR
    vs
    cv
    #
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    cI
    cD
    cif
    #
    csb
    cR
    @2
    c.le
    wbr
    #
    vs
    cR
    cI
    csb
    #
    vs
    cR
    cD
    csb
    #
    cif
    #
    vs
    cR
    cN
    csb
    cC
    vs
    cR
    @4
    @8
    cA
    vs
    @8
    wnfc
    @0
    @5
    vs
    @6
    @7
    @5
    vs
    nfv
    vs
    cR
    cI
    nfcsb1v
    vs
    cR
    cD
    nfcsb1v
    nfif
    a1i
    @1
    cR
    wceq
    @3
    @5
    cI
    cD
    @6
    @7
    @1
    cR
    @2
    c.le
    breq1
    vs
    cR
    cI
    csbeq1a
    vs
    cR
    cD
    csbeq1a
    ifbieq12d
    csbiegf
    vs
    cR
    cN
    @4
    cdleme31sn.n
    csbeq2i
    cdleme31sn.c
    3eqtr4g
end
