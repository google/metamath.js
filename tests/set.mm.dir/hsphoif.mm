include "cr.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cmpt.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "ifcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "cmap.mm"
include "co.mm"
include "cvv.mm"
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
include "wb.mm"
include "reex.mm"
include "jca.mm"
include "elmapg.mm"
include "syl.mm"
include "mpbird.mm"
include "mptexg.mm"
include "feq1d.mm"

theorem hsphoif
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vj: setvar j
  let cH: class H
  let cV: class V
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vk: setvar k
  assume hsphoif.h: |- H = ( x e. RR |-> ( a e. ( RR ^m X ) |-> ( j e. X |-> if ( j e. Y , ( a ` j ) , if ( ( a ` j ) <_ x , ( a ` j ) , x ) ) ) ) )
  assume hsphoif.a: |- ( ph -> A e. RR )
  assume hsphoif.x: |- ( ph -> X e. V )
  assume hsphoif.b: |- ( ph -> B : X --> RR )

  disjoint A a
  disjoint A j
  disjoint A x
  disjoint a j
  disjoint a x
  disjoint j x
  disjoint B a
  disjoint B j
  disjoint X a
  disjoint X j
  disjoint X x
  disjoint Y a
  disjoint Y x
  disjoint a ph
  disjoint j ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( ( H ` A ) ` B ) : X --> RR )

  proof
    wph
    cX
    cr
    cB
    cA
    cH
    cfv
    #
    cfv
    #
    wf
    cX
    cr
    vj
    cX
    vj
    cv
    #
    cY
    wcel
    #
    @2
    cB
    cfv
    #
    @4
    cA
    cle
    wbr
    #
    @4
    cA
    cif
    #
    cif
    #
    cmpt
    #
    wf
    wph
    vj
    cX
    @7
    cr
    @8
    wph
    @2
    cX
    wcel
    #
    wa
    #
    @3
    @4
    @6
    cr
    wph
    cX
    cr
    @2
    cB
    hsphoif.b
    ffvelrnda
    #
    @10
    @5
    @4
    cA
    cr
    @11
    wph
    cA
    cr
    wcel
    @9
    hsphoif.a
    adantr
    ifcld
    ifcld
    @8
    eqid
    fmptd
    wph
    cX
    cr
    @1
    @8
    wph
    va
    cB
    vj
    cX
    @3
    @2
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
    @8
    cr
    cX
    cmap
    co
    #
    @0
    cvv
    wph
    vx
    cA
    va
    @18
    vj
    cX
    @3
    @13
    @13
    vx
    cv
    #
    cle
    wbr
    #
    @13
    @19
    cif
    #
    cif
    #
    cmpt
    #
    cmpt
    #
    va
    @18
    @17
    cmpt
    #
    cr
    cH
    cvv
    cH
    vx
    cr
    @24
    cmpt
    wceq
    wph
    hsphoif.h
    a1i
    @19
    cA
    wceq
    #
    @24
    @25
    wceq
    wph
    @26
    va
    @18
    @23
    @17
    @26
    vj
    cX
    @22
    @16
    @26
    @3
    @21
    @15
    @13
    @26
    @20
    @14
    @19
    cA
    @13
    @19
    cA
    @13
    cle
    breq2
    @26
    id
    ifbieq2d
    ifeq2d
    mpteq2dv
    mpteq2dv
    adantl
    hsphoif.a
    @25
    cvv
    wcel
    wph
    va
    @18
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
    @8
    wceq
    wph
    @27
    vj
    cX
    @16
    @7
    @27
    @3
    @13
    @4
    @15
    @6
    @2
    @12
    cB
    fveq1
    #
    @27
    @14
    @5
    @13
    @4
    cA
    @27
    @13
    @4
    cA
    cle
    @28
    breq1d
    @28
    ifbieq1d
    ifeq12d
    mpteq2dv
    adantl
    wph
    cB
    @18
    wcel
    #
    cX
    cr
    cB
    wf
    #
    hsphoif.b
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
    @29
    @30
    wb
    wph
    @31
    @32
    @31
    wph
    reex
    a1i
    hsphoif.x
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
    @32
    @8
    cvv
    wcel
    hsphoif.x
    vj
    cX
    @7
    cV
    mptexg
    syl
    fvmptd
    feq1d
    mpbird
end
