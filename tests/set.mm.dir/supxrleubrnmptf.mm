include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "csb.mm"
include "wral.mm"
include "wb.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvmptf.mm"
include "rneqi.mm"
include "supeq1i.mm"
include "breq1i.mm"
include "a1i.mm"
include "nfv.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "nfcri.mm"
include "nfan.mm"
include "nfel1.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "supxrleubrnmpt.mm"
include "nfbr.mm"
include "eqcom.mm"
include "imbi1i.mm"
include "imbi2i.mm"
include "bitri.mm"
include "mpbi.mm"
include "breq1d.mm"
include "cbvralf.mm"
include "3bitrd.mm"

theorem supxrleubrnmptf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  assume supxrleubrnmptf.x: |- F/ x ph
  assume supxrleubrnmptf.a: |- F/_ x A
  assume supxrleubrnmptf.n: |- F/_ x C
  assume supxrleubrnmptf.b: |- ( ( ph /\ x e. A ) -> B e. RR* )
  assume supxrleubrnmptf.c: |- ( ph -> C e. RR* )


  assert |- ( ph -> ( sup ( ran ( x e. A |-> B ) , RR* , < ) <_ C <-> A. x e. A B <_ C ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cC
    cle
    wbr
    #
    vy
    cA
    vx
    vy
    cv
    #
    cB
    csb
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cC
    cle
    wbr
    #
    @5
    cC
    cle
    wbr
    #
    vy
    cA
    wral
    #
    cB
    cC
    cle
    wbr
    #
    vx
    cA
    wral
    #
    @3
    @9
    wb
    wph
    @2
    @8
    cC
    cle
    cxr
    @1
    @7
    clt
    @0
    @6
    vx
    vy
    cA
    cB
    @5
    supxrleubrnmptf.a
    vy
    cA
    nfcv
    #
    vy
    cB
    nfcv
    vx
    @4
    cB
    nfcsb1v
    #
    vx
    @4
    cB
    csbeq1a
    #
    cbvmptf
    rneqi
    supeq1i
    breq1i
    a1i
    wph
    vy
    cA
    @5
    cC
    wph
    vy
    nfv
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
    cxr
    wcel
    #
    wi
    wph
    @4
    cA
    wcel
    #
    wa
    #
    @5
    cxr
    wcel
    #
    wi
    vx
    vy
    @22
    @23
    vx
    wph
    @21
    vx
    supxrleubrnmptf.x
    vx
    vy
    cA
    supxrleubrnmptf.a
    nfcri
    nfan
    vx
    @5
    cxr
    @15
    nfel1
    nfim
    @17
    @4
    wceq
    #
    @19
    @22
    @20
    @23
    @24
    @18
    @21
    wph
    @17
    @4
    cA
    eleq1
    anbi2d
    @24
    cB
    @5
    cxr
    @16
    eleq1d
    imbi12d
    supxrleubrnmptf.b
    chvar
    supxrleubrnmptf.c
    supxrleubrnmpt
    @11
    @13
    wb
    wph
    @10
    @12
    vy
    vx
    cA
    @14
    supxrleubrnmptf.a
    vx
    @5
    cC
    cle
    @15
    vx
    cle
    nfcv
    supxrleubrnmptf.n
    nfbr
    @12
    vy
    nfv
    @4
    @17
    wceq
    #
    @5
    cB
    cC
    cle
    @24
    cB
    @5
    wceq
    #
    wi
    #
    @25
    @5
    cB
    wceq
    #
    wi
    #
    @16
    @27
    @25
    @26
    wi
    @29
    @24
    @25
    @26
    @17
    @4
    eqcom
    imbi1i
    @26
    @28
    @25
    cB
    @5
    eqcom
    imbi2i
    bitri
    mpbi
    breq1d
    cbvralf
    a1i
    3bitrd
end
