include "cmpt.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "eqid.mm"
include "fmptdf.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "csb.mm"
include "wi.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcv.mm"
include "nfcsb1.mm"
include "nfbr.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "csbeq1a.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "simpr.mm"
include "simpl.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "syl2anc.mm"
include "fvmptf.mm"
include "nfel.mm"
include "mpbird.mm"
include "sge0le.mm"

theorem sge0lempt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vy: setvar y
  let vk: setvar k
  assume sge0lempt.xph: |- F/ x ph
  assume sge0lempt.a: |- ( ph -> A e. V )
  assume sge0lempt.b: |- ( ( ph /\ x e. A ) -> B e. ( 0 [,] +oo ) )
  assume sge0lempt.c: |- ( ( ph /\ x e. A ) -> C e. ( 0 [,] +oo ) )
  assume sge0lempt.le: |- ( ( ph /\ x e. A ) -> B <_ C )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( x e. A |-> B ) ) <_ ( sum^ ` ( x e. A |-> C ) ) )

  proof
    wph
    vy
    vx
    cA
    cB
    cmpt
    #
    vx
    cA
    cC
    cmpt
    #
    cV
    cA
    sge0lempt.a
    wph
    vx
    cA
    cB
    cc0
    cpnf
    cicc
    co
    #
    @0
    sge0lempt.xph
    sge0lempt.b
    @0
    eqid
    #
    fmptdf
    wph
    vx
    cA
    cC
    @2
    @1
    sge0lempt.xph
    sge0lempt.c
    @1
    eqid
    #
    fmptdf
    wph
    vy
    cv
    #
    cA
    wcel
    #
    wa
    #
    @5
    @0
    cfv
    #
    @5
    @1
    cfv
    #
    cle
    wbr
    vx
    @5
    cB
    csb
    #
    vx
    @5
    cC
    csb
    #
    cle
    wbr
    #
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    cB
    cC
    cle
    wbr
    #
    wi
    @7
    @12
    wi
    vx
    vy
    @7
    @12
    vx
    wph
    @6
    vx
    sge0lempt.xph
    @6
    vx
    nfv
    nfan
    #
    vx
    @10
    @11
    cle
    vx
    @5
    cB
    vx
    @5
    nfcv
    #
    nfcsb1
    #
    vx
    cle
    nfcv
    vx
    @5
    cC
    @18
    nfcsb1
    #
    nfbr
    nfim
    @13
    @5
    wceq
    #
    @15
    @7
    @16
    @12
    @21
    @14
    @6
    wph
    @13
    @5
    cA
    eleq1
    anbi2d
    #
    @21
    cB
    @10
    cC
    @11
    cle
    vx
    @5
    cB
    csbeq1a
    #
    vx
    @5
    cC
    csbeq1a
    #
    breq12d
    imbi12d
    sge0lempt.le
    chvar
    @7
    @8
    @10
    @9
    @11
    cle
    @7
    @6
    @10
    @2
    wcel
    #
    @8
    @10
    wceq
    wph
    @6
    simpr
    #
    @7
    wph
    @6
    @25
    wph
    @6
    simpl
    #
    @26
    @15
    cB
    @2
    wcel
    #
    wi
    @7
    @25
    wi
    vx
    vy
    @7
    @25
    vx
    @17
    vx
    @10
    @2
    @19
    nfel1
    nfim
    @21
    @15
    @7
    @28
    @25
    @22
    @21
    cB
    @10
    @2
    @23
    eleq1d
    imbi12d
    sge0lempt.b
    chvar
    syl2anc
    vx
    @5
    cB
    @10
    cA
    @0
    @2
    @18
    @19
    @23
    @3
    fvmptf
    syl2anc
    @7
    @6
    @11
    @2
    wcel
    #
    @9
    @11
    wceq
    @26
    @7
    wph
    @6
    @29
    @27
    @26
    @15
    cC
    @2
    wcel
    #
    wi
    @7
    @29
    wi
    vx
    vy
    @7
    @29
    vx
    @17
    vx
    @11
    @2
    @20
    vx
    @2
    nfcv
    nfel
    nfim
    @21
    @15
    @7
    @30
    @29
    @22
    @21
    cC
    @11
    @2
    @24
    eleq1d
    imbi12d
    sge0lempt.c
    chvar
    syl2anc
    vx
    @5
    cC
    @11
    cA
    @1
    @2
    @18
    @20
    @24
    @4
    fvmptf
    syl2anc
    breq12d
    mpbird
    sge0le
end
