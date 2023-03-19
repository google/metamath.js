include "wcel.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "csb.mm"
include "cif.mm"
include "wceq.mm"
include "eqid.mm"
include "cdleme31sn.mm"
include "adantr.mm"
include "cv.mm"
include "iffalse.mm"
include "csbeq2i.mm"
include "syl6eq.mm"
include "nfcvd.mm"
include "oveq1.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "csbiegf.mm"
include "sylan9eqr.mm"
include "eqtrd.mm"
include "syl6eqr.mm"

theorem cdleme31sn2
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cI: class I
  let c.or: class .\/
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let vs: setvar s
  assume cdleme32sn2.d: |- D = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdleme31sn2.n: |- N = if ( s .<_ ( P .\/ Q ) , I , D )
  assume cdleme31sn2.c: |- C = ( ( R .\/ U ) ./\ ( Q .\/ ( ( P .\/ R ) ./\ W ) ) )

  disjoint A s
  disjoint .\/ s
  disjoint .<_ s
  disjoint ./\ s
  disjoint P s
  disjoint Q s
  disjoint R s
  disjoint U s
  disjoint W s
  assert |- ( ( R e. A /\ -. R .<_ ( P .\/ Q ) ) -> [_ R / s ]_ N = C )

  proof
    cR
    cA
    wcel
    #
    cR
    cP
    cQ
    c.or
    co
    c.le
    wbr
    #
    wn
    #
    wa
    #
    vs
    cR
    cN
    csb
    #
    cR
    cU
    c.or
    co
    #
    cQ
    cP
    cR
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    #
    cC
    @3
    @4
    @1
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
    @9
    @0
    @4
    @12
    wceq
    @2
    cA
    @12
    cD
    cP
    cQ
    cR
    cI
    c.or
    c.le
    cN
    vs
    cdleme31sn2.n
    @12
    eqid
    cdleme31sn
    adantr
    @2
    @0
    @12
    vs
    cR
    vs
    cv
    #
    cU
    c.or
    co
    #
    cQ
    cP
    @13
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    #
    csb
    #
    @9
    @2
    @12
    @11
    @19
    @1
    @10
    @11
    iffalse
    vs
    cR
    cD
    @18
    cdleme32sn2.d
    csbeq2i
    syl6eq
    vs
    cR
    @18
    @9
    cA
    @0
    vs
    @9
    nfcvd
    @13
    cR
    wceq
    #
    @14
    @5
    @17
    @8
    c.an
    @13
    cR
    cU
    c.or
    oveq1
    @20
    @16
    @7
    cQ
    c.or
    @20
    @15
    @6
    cW
    c.an
    @13
    cR
    cP
    c.or
    oveq2
    oveq1d
    oveq2d
    oveq12d
    csbiegf
    sylan9eqr
    eqtrd
    cdleme31sn2.c
    syl6eqr
end
