include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cbs.mm"
include "wa.mm"
include "simpr.mm"
include "csymg.mm"
include "eqid.mm"
include "symgfv.mm"
include "3ad2antl2.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "matecl.mm"
include "syl3anc.mm"
include "ralrimiva.mm"

theorem matepm2cl
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let vn: setvar n
  let cM: class M
  let cN: class N
  assume matepmcl.a: |- A = ( N Mat R )
  assume matepmcl.b: |- B = ( Base ` A )
  assume matepmcl.p: |- P = ( Base ` ( SymGrp ` N ) )

  disjoint B n
  disjoint M n
  disjoint P n
  disjoint R n
  disjoint Q n
  assert |- ( ( R e. Ring /\ Q e. P /\ M e. B ) -> A. n e. N ( n M ( Q ` n ) ) e. ( Base ` R ) )

  proof
    cR
    crg
    wcel
    #
    cQ
    cP
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    vn
    cv
    #
    @4
    cQ
    cfv
    #
    cM
    co
    cR
    cbs
    cfv
    #
    wcel
    #
    vn
    cN
    @3
    @4
    cN
    wcel
    #
    wa
    @8
    @5
    cN
    wcel
    #
    cM
    cA
    cbs
    cfv
    #
    wcel
    #
    @7
    @3
    @8
    simpr
    @1
    @0
    @8
    @9
    @2
    cN
    cP
    cQ
    cN
    csymg
    cfv
    #
    @4
    @12
    eqid
    matepmcl.p
    symgfv
    3ad2antl2
    @3
    @11
    @8
    @2
    @0
    @11
    @1
    @2
    @11
    cB
    @10
    cM
    matepmcl.b
    eleq2i
    biimpi
    3ad2ant3
    adantr
    cA
    cR
    @4
    @5
    @6
    cM
    cN
    matepmcl.a
    @6
    eqid
    matecl
    syl3anc
    ralrimiva
end
