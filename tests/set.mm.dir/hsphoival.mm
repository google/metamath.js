include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cvv.mm"
include "cmpt.mm"
include "cr.mm"
include "cmap.mm"
include "co.mm"
include "wceq.mm"
include "a1i.mm"
include "breq2.mm"
include "id.mm"
include "ifbieq2d.mm"
include "ifeq2d.mm"
include "mpteq2dv.mm"
include "adantl.mm"
include "ovex.mm"
include "mptex.mm"
include "fvmptd.mm"
include "fveq1.mm"
include "breq1d.mm"
include "ifbieq1d.mm"
include "ifeq12d.mm"
include "wf.mm"
include "wa.mm"
include "wb.mm"
include "reex.mm"
include "jca.mm"
include "elmapg.mm"
include "syl.mm"
include "mpbird.mm"
include "mptexg.mm"
include "eleq1.mm"
include "fveq2.mm"
include "ifbieq12d.mm"
include "ffvelrnd.mm"
include "ifcld.mm"
include "ifexg.mm"
include "syl2anc.mm"

theorem hsphoival
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vj: setvar j
  let cH: class H
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vk: setvar k
  assume hsphoival.h: |- H = ( x e. RR |-> ( a e. ( RR ^m X ) |-> ( j e. X |-> if ( j e. Y , ( a ` j ) , if ( ( a ` j ) <_ x , ( a ` j ) , x ) ) ) ) )
  assume hsphoival.a: |- ( ph -> A e. RR )
  assume hsphoival.x: |- ( ph -> X e. V )
  assume hsphoival.b: |- ( ph -> B : X --> RR )
  assume hsphoival.k: |- ( ph -> K e. X )

  disjoint A a
  disjoint A j
  disjoint A x
  disjoint a j
  disjoint a x
  disjoint j x
  disjoint B a
  disjoint B j
  disjoint K j
  disjoint X a
  disjoint X j
  disjoint X x
  disjoint Y a
  disjoint Y j
  disjoint Y x
  disjoint a ph
  disjoint j ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( ( ( H ` A ) ` B ) ` K ) = if ( K e. Y , ( B ` K ) , if ( ( B ` K ) <_ A , ( B ` K ) , A ) ) )

  proof
    wph
    vj
    cK
    vj
    cv
    #
    cY
    wcel
    #
    @0
    cB
    cfv
    #
    @2
    cA
    cle
    wbr
    #
    @2
    cA
    cif
    #
    cif
    #
    cK
    cY
    wcel
    #
    cK
    cB
    cfv
    #
    @7
    cA
    cle
    wbr
    #
    @7
    cA
    cif
    #
    cif
    #
    cX
    cB
    cA
    cH
    cfv
    #
    cfv
    cvv
    wph
    va
    cB
    vj
    cX
    @1
    @0
    va
    cv
    #
    cfv
    #
    @13
    cA
    cle
    wbr
    #
    @13
    cA
    cif
    #
    cif
    #
    cmpt
    #
    vj
    cX
    @5
    cmpt
    #
    cr
    cX
    cmap
    co
    #
    @11
    cvv
    wph
    vx
    cA
    va
    @19
    vj
    cX
    @1
    @13
    @13
    vx
    cv
    #
    cle
    wbr
    #
    @13
    @20
    cif
    #
    cif
    #
    cmpt
    #
    cmpt
    #
    va
    @19
    @17
    cmpt
    #
    cr
    cH
    cvv
    cH
    vx
    cr
    @25
    cmpt
    wceq
    wph
    hsphoival.h
    a1i
    @20
    cA
    wceq
    #
    @25
    @26
    wceq
    wph
    @27
    va
    @19
    @24
    @17
    @27
    vj
    cX
    @23
    @16
    @27
    @1
    @22
    @15
    @13
    @27
    @21
    @14
    @20
    cA
    @13
    @20
    cA
    @13
    cle
    breq2
    @27
    id
    ifbieq2d
    ifeq2d
    mpteq2dv
    mpteq2dv
    adantl
    hsphoival.a
    @26
    cvv
    wcel
    wph
    va
    @19
    @17
    cr
    cX
    cmap
    ovex
    mptex
    a1i
    fvmptd
    @12
    cB
    wceq
    #
    @17
    @18
    wceq
    wph
    @28
    vj
    cX
    @16
    @5
    @28
    @1
    @13
    @2
    @15
    @4
    @0
    @12
    cB
    fveq1
    #
    @28
    @14
    @3
    @13
    @2
    cA
    @28
    @13
    @2
    cA
    cle
    @29
    breq1d
    @29
    ifbieq1d
    ifeq12d
    mpteq2dv
    adantl
    wph
    cB
    @19
    wcel
    #
    cX
    cr
    cB
    wf
    #
    hsphoival.b
    wph
    cr
    cvv
    wcel
    #
    cX
    cV
    wcel
    #
    wa
    @30
    @31
    wb
    wph
    @32
    @33
    @32
    wph
    reex
    a1i
    hsphoival.x
    jca
    cr
    cX
    cB
    cvv
    cV
    elmapg
    syl
    mpbird
    wph
    @33
    @18
    cvv
    wcel
    hsphoival.x
    vj
    cX
    @5
    cV
    mptexg
    syl
    fvmptd
    @0
    cK
    wceq
    #
    @5
    @10
    wceq
    wph
    @34
    @1
    @6
    @2
    @4
    @7
    @9
    @0
    cK
    cY
    eleq1
    @0
    cK
    cB
    fveq2
    #
    @34
    @3
    @8
    @2
    @7
    cA
    @34
    @2
    @7
    cA
    cle
    @35
    breq1d
    @35
    ifbieq1d
    ifbieq12d
    adantl
    hsphoival.k
    wph
    @7
    cr
    wcel
    @9
    cr
    wcel
    @10
    cvv
    wcel
    wph
    cX
    cr
    cK
    cB
    hsphoival.b
    hsphoival.k
    ffvelrnd
    #
    wph
    @8
    @7
    cA
    cr
    @36
    hsphoival.a
    ifcld
    @6
    @7
    @9
    cr
    cr
    ifexg
    syl2anc
    fvmptd
end
