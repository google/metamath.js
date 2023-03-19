include "chj.mm"
include "co.mm"
include "wcel.mm"
include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "cph.mm"
include "cpjh.mm"
include "cva.mm"
include "osumi.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "cch.mm"
include "wceq.mm"
include "chjcli.mm"
include "pjid.mm"
include "mpan.mm"
include "sylan9eqr.mm"
include "chil.mm"
include "cheli.mm"
include "pjsumi.mm"
include "imp.mm"
include "sylan.mm"
include "eqtr3d.mm"

theorem pjdsi
  let cA: class A
  let cG: class G
  let cH: class H
  assume pjsumt.1: |- G e. CH
  assume pjsumt.2: |- H e. CH


  assert |- ( ( A e. ( G vH H ) /\ G C_ ( _|_ ` H ) ) -> A = ( ( ( projh ` G ) ` A ) +h ( ( projh ` H ) ` A ) ) )

  proof
    cA
    cG
    cH
    chj
    co
    #
    wcel
    #
    cG
    cH
    cort
    cfv
    wss
    #
    wa
    cA
    cG
    cH
    cph
    co
    #
    cpjh
    cfv
    #
    cfv
    #
    cA
    cA
    cG
    cpjh
    cfv
    cfv
    cA
    cH
    cpjh
    cfv
    cfv
    cva
    co
    #
    @2
    @1
    @5
    cA
    @0
    cpjh
    cfv
    #
    cfv
    #
    cA
    @2
    cA
    @4
    @7
    @2
    @3
    @0
    cpjh
    cG
    cH
    pjsumt.1
    pjsumt.2
    osumi
    fveq2d
    fveq1d
    @0
    cch
    wcel
    @1
    @8
    cA
    wceq
    cG
    cH
    pjsumt.1
    pjsumt.2
    chjcli
    #
    cA
    @0
    pjid
    mpan
    sylan9eqr
    @1
    cA
    chil
    wcel
    #
    @2
    @5
    @6
    wceq
    #
    cA
    @0
    @9
    cheli
    @10
    @2
    @11
    cA
    cG
    cH
    pjsumt.1
    pjsumt.2
    pjsumi
    imp
    sylan
    eqtr3d
end
