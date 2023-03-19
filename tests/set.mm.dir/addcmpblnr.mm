include "cpp.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cop.mm"
include "cer.mm"
include "wbr.mm"
include "cnp.mm"
include "wcel.mm"
include "oveq12.mm"
include "wb.mm"
include "addclpr.mm"
include "anim12i.mm"
include "an4s.mm"
include "enrbreq.mm"
include "syl.mm"
include "addcompr.mm"
include "oveq1i.mm"
include "addasspr.mm"
include "3eqtr3i.mm"
include "oveq2i.mm"
include "3eqtr4i.mm"
include "eqeq12i.mm"
include "syl6bb.mm"
include "syl5ibr.mm"

theorem addcmpblnr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( ( ( A e. P. /\ B e. P. ) /\ ( C e. P. /\ D e. P. ) ) /\ ( ( F e. P. /\ G e. P. ) /\ ( R e. P. /\ S e. P. ) ) ) -> ( ( ( A +P. D ) = ( B +P. C ) /\ ( F +P. S ) = ( G +P. R ) ) -> <. ( A +P. F ) , ( B +P. G ) >. ~R <. ( C +P. R ) , ( D +P. S ) >. ) )

  proof
    cA
    cD
    cpp
    co
    #
    cB
    cC
    cpp
    co
    #
    wceq
    cF
    cS
    cpp
    co
    #
    cG
    cR
    cpp
    co
    #
    wceq
    wa
    cA
    cF
    cpp
    co
    #
    cB
    cG
    cpp
    co
    #
    cop
    cC
    cR
    cpp
    co
    #
    cD
    cS
    cpp
    co
    #
    cop
    cer
    wbr
    #
    cA
    cnp
    wcel
    #
    cB
    cnp
    wcel
    #
    wa
    #
    cC
    cnp
    wcel
    #
    cD
    cnp
    wcel
    #
    wa
    #
    wa
    cF
    cnp
    wcel
    #
    cG
    cnp
    wcel
    #
    wa
    #
    cR
    cnp
    wcel
    #
    cS
    cnp
    wcel
    #
    wa
    #
    wa
    wa
    #
    @0
    @2
    cpp
    co
    #
    @1
    @3
    cpp
    co
    #
    wceq
    #
    @0
    @1
    @2
    @3
    cpp
    oveq12
    @21
    @8
    @4
    @7
    cpp
    co
    #
    @5
    @6
    cpp
    co
    #
    wceq
    #
    @24
    @21
    @4
    cnp
    wcel
    #
    @5
    cnp
    wcel
    #
    wa
    #
    @6
    cnp
    wcel
    #
    @7
    cnp
    wcel
    #
    wa
    #
    wa
    #
    @8
    @27
    wb
    @11
    @17
    @14
    @20
    @34
    @11
    @17
    wa
    @30
    @14
    @20
    wa
    @33
    @9
    @15
    @10
    @16
    @30
    @9
    @15
    wa
    @28
    @10
    @16
    wa
    @29
    cA
    cF
    addclpr
    cB
    cG
    addclpr
    anim12i
    an4s
    @12
    @18
    @13
    @19
    @33
    @12
    @18
    wa
    @31
    @13
    @19
    wa
    @32
    cC
    cR
    addclpr
    cD
    cS
    addclpr
    anim12i
    an4s
    anim12i
    an4s
    @4
    @5
    @6
    @7
    enrbreq
    syl
    @25
    @22
    @26
    @23
    cA
    cF
    @7
    cpp
    co
    #
    cpp
    co
    cA
    cD
    @2
    cpp
    co
    #
    cpp
    co
    @25
    @22
    @35
    @36
    cA
    cpp
    cF
    cD
    cpp
    co
    #
    cS
    cpp
    co
    cD
    cF
    cpp
    co
    #
    cS
    cpp
    co
    @35
    @36
    @37
    @38
    cS
    cpp
    cF
    cD
    addcompr
    oveq1i
    cF
    cD
    cS
    addasspr
    cD
    cF
    cS
    addasspr
    3eqtr3i
    oveq2i
    cA
    cF
    @7
    addasspr
    cA
    cD
    @2
    addasspr
    3eqtr4i
    cB
    cG
    @6
    cpp
    co
    #
    cpp
    co
    cB
    cC
    @3
    cpp
    co
    #
    cpp
    co
    @26
    @23
    @39
    @40
    cB
    cpp
    cG
    cC
    cpp
    co
    #
    cR
    cpp
    co
    cC
    cG
    cpp
    co
    #
    cR
    cpp
    co
    @39
    @40
    @41
    @42
    cR
    cpp
    cG
    cC
    addcompr
    oveq1i
    cG
    cC
    cR
    addasspr
    cC
    cG
    cR
    addasspr
    3eqtr3i
    oveq2i
    cB
    cG
    @6
    addasspr
    cB
    cC
    @3
    addasspr
    3eqtr4i
    eqeq12i
    syl6bb
    syl5ibr
end
