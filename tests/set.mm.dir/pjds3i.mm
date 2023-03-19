include "chj.mm"
include "co.mm"
include "wcel.mm"
include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "cpjh.mm"
include "cva.mm"
include "cph.mm"
include "wceq.mm"
include "simpl.mm"
include "choccli.mm"
include "chlubii.mm"
include "chjcli.mm"
include "pjdsi.mm"
include "syl2an.mm"
include "osumi.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "oveq1d.mm"
include "ad2antlr.mm"
include "chil.mm"
include "cheli.mm"
include "pjsumi.mm"
include "imp.mm"
include "sylan.mm"
include "adantr.mm"
include "3eqtr2d.mm"

theorem pjds3i
  let cA: class A
  let cF: class F
  let cG: class G
  let cH: class H
  assume pjds3.1: |- F e. CH
  assume pjds3.2: |- G e. CH
  assume pjds3.3: |- H e. CH


  assert |- ( ( ( A e. ( ( F vH G ) vH H ) /\ F C_ ( _|_ ` G ) ) /\ ( F C_ ( _|_ ` H ) /\ G C_ ( _|_ ` H ) ) ) -> A = ( ( ( ( projh ` F ) ` A ) +h ( ( projh ` G ) ` A ) ) +h ( ( projh ` H ) ` A ) ) )

  proof
    cA
    cF
    cG
    chj
    co
    #
    cH
    chj
    co
    #
    wcel
    #
    cF
    cG
    cort
    cfv
    wss
    #
    wa
    #
    cF
    cH
    cort
    cfv
    #
    wss
    cG
    @5
    wss
    wa
    #
    wa
    cA
    cA
    @0
    cpjh
    cfv
    #
    cfv
    #
    cA
    cH
    cpjh
    cfv
    cfv
    #
    cva
    co
    #
    cA
    cF
    cG
    cph
    co
    #
    cpjh
    cfv
    #
    cfv
    #
    @9
    cva
    co
    #
    cA
    cF
    cpjh
    cfv
    cfv
    cA
    cG
    cpjh
    cfv
    cfv
    cva
    co
    #
    @9
    cva
    co
    #
    @4
    @2
    @0
    @5
    wss
    cA
    @10
    wceq
    @6
    @2
    @3
    simpl
    cF
    cG
    @5
    pjds3.1
    pjds3.2
    cH
    pjds3.3
    choccli
    chlubii
    cA
    @0
    cH
    cF
    cG
    pjds3.1
    pjds3.2
    chjcli
    #
    pjds3.3
    pjdsi
    syl2an
    @3
    @14
    @10
    wceq
    @2
    @6
    @3
    @13
    @8
    @9
    cva
    @3
    cA
    @12
    @7
    @3
    @11
    @0
    cpjh
    cF
    cG
    pjds3.1
    pjds3.2
    osumi
    fveq2d
    fveq1d
    oveq1d
    ad2antlr
    @4
    @14
    @16
    wceq
    @6
    @4
    @13
    @15
    @9
    cva
    @2
    cA
    chil
    wcel
    #
    @3
    @13
    @15
    wceq
    #
    cA
    @1
    @0
    cH
    @17
    pjds3.3
    chjcli
    cheli
    @18
    @3
    @19
    cA
    cF
    cG
    pjds3.1
    pjds3.2
    pjsumi
    imp
    sylan
    oveq1d
    adantr
    3eqtr2d
end
