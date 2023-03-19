include "chst.mm"
include "wcel.mm"
include "cch.mm"
include "wa.mm"
include "cfv.mm"
include "cno.mm"
include "c1.mm"
include "wceq.mm"
include "chil.mm"
include "c0v.mm"
include "cva.mm"
include "co.mm"
include "hstcl.mm"
include "ax-hvaddid.mm"
include "syl.mm"
include "adantr.mm"
include "cort.mm"
include "c2.mm"
include "cexp.mm"
include "cc0.mm"
include "cmin.mm"
include "caddc.mm"
include "cc.mm"
include "ax-1cn.mm"
include "cr.mm"
include "choccl.mm"
include "sylan2.mm"
include "normcl.mm"
include "resqcld.mm"
include "recnd.mm"
include "pncan2.mm"
include "sylancr.mm"
include "oveq1.mm"
include "sq1.mm"
include "syl6req.mm"
include "oveq1d.mm"
include "hstnmoc.mm"
include "sylan9eqr.mm"
include "eqtr3d.mm"
include "1m1e0.mm"
include "syl6eq.mm"
include "ex.mm"
include "wb.mm"
include "sqeq0.mm"
include "norm-i.mm"
include "bitrd.mm"
include "sylibd.mm"
include "imp.mm"
include "oveq2d.mm"
include "hstoc.mm"
include "fveq2.mm"
include "hst1a.mm"
include "impbida.mm"

theorem hst1h
  let cA: class A
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let cB: class B


  assert |- ( ( S e. CHStates /\ A e. CH ) -> ( ( normh ` ( S ` A ) ) = 1 <-> ( S ` A ) = ( S ` ~H ) ) )

  proof
    cS
    chst
    wcel
    #
    cA
    cch
    wcel
    #
    wa
    #
    cA
    cS
    cfv
    #
    cno
    cfv
    #
    c1
    wceq
    #
    @3
    chil
    cS
    cfv
    #
    wceq
    #
    @2
    @5
    wa
    #
    @3
    c0v
    cva
    co
    #
    @3
    @6
    @2
    @9
    @3
    wceq
    #
    @5
    @2
    @3
    chil
    wcel
    @10
    cA
    cS
    hstcl
    @3
    ax-hvaddid
    syl
    adantr
    @8
    @3
    cA
    cort
    cfv
    #
    cS
    cfv
    #
    cva
    co
    #
    @9
    @6
    @8
    @12
    c0v
    @3
    cva
    @2
    @5
    @12
    c0v
    wceq
    #
    @2
    @5
    @12
    cno
    cfv
    #
    c2
    cexp
    co
    #
    cc0
    wceq
    #
    @14
    @2
    @5
    @17
    @8
    @16
    c1
    c1
    cmin
    co
    #
    cc0
    @8
    c1
    @16
    caddc
    co
    #
    c1
    cmin
    co
    #
    @16
    @18
    @2
    @20
    @16
    wceq
    #
    @5
    @2
    c1
    cc
    wcel
    @16
    cc
    wcel
    @21
    ax-1cn
    @2
    @16
    @2
    @15
    @2
    @12
    chil
    wcel
    #
    @15
    cr
    wcel
    @1
    @0
    @11
    cch
    wcel
    @22
    cA
    choccl
    @11
    cS
    hstcl
    sylan2
    #
    @12
    normcl
    syl
    #
    resqcld
    recnd
    c1
    @16
    pncan2
    sylancr
    adantr
    @8
    @19
    c1
    c1
    cmin
    @5
    @2
    @19
    @4
    c2
    cexp
    co
    #
    @16
    caddc
    co
    c1
    @5
    c1
    @25
    @16
    caddc
    @5
    @25
    c1
    c2
    cexp
    co
    c1
    @4
    c1
    c2
    cexp
    oveq1
    sq1
    syl6req
    oveq1d
    cA
    cS
    hstnmoc
    sylan9eqr
    oveq1d
    eqtr3d
    1m1e0
    syl6eq
    ex
    @2
    @17
    @15
    cc0
    wceq
    #
    @14
    @2
    @15
    cc
    wcel
    @17
    @26
    wb
    @2
    @15
    @24
    recnd
    @15
    sqeq0
    syl
    @2
    @22
    @26
    @14
    wb
    @23
    @12
    norm-i
    syl
    bitrd
    sylibd
    imp
    oveq2d
    @2
    @13
    @6
    wceq
    @5
    cA
    cS
    hstoc
    adantr
    eqtr3d
    eqtr3d
    @7
    @2
    @4
    @6
    cno
    cfv
    #
    c1
    @3
    @6
    cno
    fveq2
    @0
    @27
    c1
    wceq
    @1
    cS
    hst1a
    adantr
    sylan9eqr
    impbida
end
