include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "csqrt.mm"
include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "cle.mm"
include "wbr.mm"
include "axsegconlem5.mm"
include "adantl.mm"
include "cr.mm"
include "wb.mm"
include "axsegconlem4.mm"
include "3adant3.mm"
include "addge01.mm"
include "syl2an.mm"
include "mpbid.mm"
include "clt.mm"
include "adantr.mm"
include "readdcl.mm"
include "0red.mm"
include "axsegconlem6.mm"
include "ltletrd.mm"
include "divelunit.mm"
include "syl22anc.mm"
include "mpbird.mm"

theorem axsegconlem7
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let cN: class N
  let vp: setvar p
  assume axsegconlem2.1: |- S = sum_ p e. ( 1 ... N ) ( ( ( A ` p ) - ( B ` p ) ) ^ 2 )
  assume axsegconlem7.2: |- T = sum_ p e. ( 1 ... N ) ( ( ( C ` p ) - ( D ` p ) ) ^ 2 )

  disjoint A p
  disjoint B p
  disjoint C p
  disjoint D p
  disjoint N p
  assert |- ( ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ A =/= B ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> ( ( sqrt ` S ) / ( ( sqrt ` S ) + ( sqrt ` T ) ) ) e. ( 0 [,] 1 ) )

  proof
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    #
    cC
    @0
    wcel
    cD
    @0
    wcel
    wa
    #
    wa
    #
    cS
    csqrt
    cfv
    #
    @7
    cT
    csqrt
    cfv
    #
    caddc
    co
    #
    cdiv
    co
    cc0
    c1
    cicc
    co
    wcel
    #
    @7
    @9
    cle
    wbr
    #
    @6
    cc0
    @8
    cle
    wbr
    #
    @11
    @5
    @12
    @4
    cC
    cD
    cT
    cN
    vp
    axsegconlem7.2
    axsegconlem5
    adantl
    @4
    @7
    cr
    wcel
    #
    @8
    cr
    wcel
    #
    @12
    @11
    wb
    @5
    @1
    @2
    @13
    @3
    cA
    cB
    cS
    cN
    vp
    axsegconlem2.1
    axsegconlem4
    3adant3
    #
    cC
    cD
    cT
    cN
    vp
    axsegconlem7.2
    axsegconlem4
    #
    @7
    @8
    addge01
    syl2an
    mpbid
    #
    @6
    @13
    cc0
    @7
    cle
    wbr
    #
    @9
    cr
    wcel
    #
    cc0
    @9
    clt
    wbr
    @10
    @11
    wb
    @4
    @13
    @5
    @15
    adantr
    #
    @4
    @18
    @5
    @1
    @2
    @18
    @3
    cA
    cB
    cS
    cN
    vp
    axsegconlem2.1
    axsegconlem5
    3adant3
    adantr
    @4
    @13
    @14
    @19
    @5
    @15
    @16
    @7
    @8
    readdcl
    syl2an
    #
    @6
    cc0
    @7
    @9
    @6
    0red
    @20
    @21
    @4
    cc0
    @7
    clt
    wbr
    @5
    cA
    cB
    cS
    cN
    vp
    axsegconlem2.1
    axsegconlem6
    adantr
    @17
    ltletrd
    @7
    @9
    divelunit
    syl22anc
    mpbird
end
