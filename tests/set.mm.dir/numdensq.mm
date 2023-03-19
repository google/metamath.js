include "cq.mm"
include "wcel.mm"
include "cnumer.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdenom.mm"
include "cgcd.mm"
include "c1.mm"
include "wceq.mm"
include "cdiv.mm"
include "wa.mm"
include "qnumdencoprm.mm"
include "oveq1d.mm"
include "cz.mm"
include "qnumcl.mm"
include "qdencl.mm"
include "nnzd.mm"
include "zgcdsq.mm"
include "syl2anc.mm"
include "sq1.mm"
include "a1i.mm"
include "3eqtr3d.mm"
include "qeqnumdivden.mm"
include "zcnd.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "sqdivd.mm"
include "eqtrd.mm"
include "cn.mm"
include "wb.mm"
include "qsqcl.mm"
include "zsqcl.mm"
include "syl.mm"
include "nnsqcld.mm"
include "qnumdenbi.mm"
include "syl3anc.mm"
include "mpbi2and.mm"

theorem numdensq
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A e. QQ -> ( ( numer ` ( A ^ 2 ) ) = ( ( numer ` A ) ^ 2 ) /\ ( denom ` ( A ^ 2 ) ) = ( ( denom ` A ) ^ 2 ) ) )

  proof
    cA
    cq
    wcel
    #
    cA
    cnumer
    cfv
    #
    c2
    cexp
    co
    #
    cA
    cdenom
    cfv
    #
    c2
    cexp
    co
    #
    cgcd
    co
    #
    c1
    wceq
    #
    cA
    c2
    cexp
    co
    #
    @2
    @4
    cdiv
    co
    #
    wceq
    #
    @7
    cnumer
    cfv
    @2
    wceq
    @7
    cdenom
    cfv
    @4
    wceq
    wa
    #
    @0
    @1
    @3
    cgcd
    co
    #
    c2
    cexp
    co
    #
    c1
    c2
    cexp
    co
    #
    @5
    c1
    @0
    @11
    c1
    c2
    cexp
    cA
    qnumdencoprm
    oveq1d
    @0
    @1
    cz
    wcel
    #
    @3
    cz
    wcel
    @12
    @5
    wceq
    cA
    qnumcl
    #
    @0
    @3
    cA
    qdencl
    #
    nnzd
    @1
    @3
    zgcdsq
    syl2anc
    @13
    c1
    wceq
    @0
    sq1
    a1i
    3eqtr3d
    @0
    @7
    @1
    @3
    cdiv
    co
    #
    c2
    cexp
    co
    @8
    @0
    cA
    @17
    c2
    cexp
    cA
    qeqnumdivden
    oveq1d
    @0
    @1
    @3
    @0
    @1
    @15
    zcnd
    @0
    @3
    @16
    nncnd
    @0
    @3
    @16
    nnne0d
    sqdivd
    eqtrd
    @0
    @7
    cq
    wcel
    @2
    cz
    wcel
    #
    @4
    cn
    wcel
    @6
    @9
    wa
    @10
    wb
    cA
    qsqcl
    @0
    @14
    @18
    @15
    @1
    zsqcl
    syl
    @0
    @3
    @16
    nnsqcld
    @7
    @2
    @4
    qnumdenbi
    syl3anc
    mpbi2and
end
