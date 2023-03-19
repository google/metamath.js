include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cbs.mm"
include "cfv.mm"
include "c1.mm"
include "c2.mm"
include "cv.mm"
include "co.mm"
include "eqid.mm"
include "mgpbas.mm"
include "cmnd.mm"
include "ringmgp.mm"
include "3ad2ant1.mm"
include "cuz.mm"
include "2eluzge1.mm"
include "a1i.mm"
include "cfz.mm"
include "wceq.mm"
include "caddc.mm"
include "cpr.mm"
include "cz.mm"
include "1z.mm"
include "fzpr.mm"
include "ax-mp.mm"
include "1p1e2.mm"
include "preq2i.mm"
include "eqtri.mm"
include "df-2.mm"
include "oveq2i.mm"
include "3eqtr4ri.mm"
include "matepmcl.mm"
include "gsummptfzcl.mm"

theorem m2detleiblem2
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let vn: setvar n
  let cG: class G
  let cM: class M
  let cN: class N
  assume m2detleiblem2.n: |- N = { 1 , 2 }
  assume m2detleiblem2.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume m2detleiblem2.a: |- A = ( N Mat R )
  assume m2detleiblem2.b: |- B = ( Base ` A )
  assume m2detleiblem2.g: |- G = ( mulGrp ` R )

  disjoint B n
  disjoint M n
  disjoint N n
  disjoint P n
  disjoint Q n
  disjoint R n
  assert |- ( ( R e. Ring /\ Q e. P /\ M e. B ) -> ( G gsum ( n e. N |-> ( ( Q ` n ) M n ) ) ) e. ( Base ` R ) )

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
    cR
    cbs
    cfv
    #
    vn
    cG
    cN
    c1
    c2
    vn
    cv
    #
    cQ
    cfv
    @5
    cM
    co
    @4
    cR
    cG
    m2detleiblem2.g
    @4
    eqid
    mgpbas
    @0
    @1
    cG
    cmnd
    wcel
    @2
    cR
    cG
    m2detleiblem2.g
    ringmgp
    3ad2ant1
    c2
    c1
    cuz
    cfv
    wcel
    @3
    2eluzge1
    a1i
    cN
    c1
    c2
    cfz
    co
    #
    wceq
    @3
    c1
    c1
    c1
    caddc
    co
    #
    cfz
    co
    #
    c1
    c2
    cpr
    #
    @6
    cN
    @8
    c1
    @7
    cpr
    #
    @9
    c1
    cz
    wcel
    @8
    @10
    wceq
    1z
    c1
    fzpr
    ax-mp
    @7
    c2
    c1
    1p1e2
    preq2i
    eqtri
    c2
    @7
    c1
    cfz
    df-2
    oveq2i
    m2detleiblem2.n
    3eqtr4ri
    a1i
    cA
    cB
    cP
    cQ
    cR
    vn
    cM
    cN
    m2detleiblem2.a
    m2detleiblem2.b
    m2detleiblem2.p
    matepmcl
    gsummptfzcl
end
