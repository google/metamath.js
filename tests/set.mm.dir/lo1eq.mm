include "cr.mm"
include "wss.mm"
include "cmpt.mm"
include "clo1.mm"
include "wcel.mm"
include "cdm.mm"
include "lo1dm.mm"
include "eqid.mm"
include "dmmptd.mm"
include "sseq1d.mm"
include "syl5ib.mm"
include "wb.mm"
include "wa.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cres.mm"
include "cin.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "simpr.mm"
include "elin.mm"
include "sylib.mm"
include "simpld.mm"
include "simprd.mm"
include "elicopnf.mm"
include "syl.mm"
include "biimpa.mm"
include "syldan.mm"
include "jca.mm"
include "mpteq2dva.mm"
include "inss1.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"
include "resres.mm"
include "ssid.mm"
include "reseq1.mm"
include "mp2b.mm"
include "3eqtr3g.mm"
include "eleq1d.mm"
include "adantr.mm"
include "wf.mm"
include "fmptd.mm"
include "lo1resb.mm"
include "3bitr4d.mm"
include "ex.mm"
include "pm5.21ndd.mm"

theorem lo1eq
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume lo1eq.1: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume lo1eq.2: |- ( ( ph /\ x e. A ) -> C e. RR )
  assume lo1eq.3: |- ( ph -> D e. RR )
  assume lo1eq.4: |- ( ( ph /\ ( x e. A /\ D <_ x ) ) -> B = C )

  disjoint A x
  disjoint D x
  disjoint ph x
  assert |- ( ph -> ( ( x e. A |-> B ) e. <_O(1) <-> ( x e. A |-> C ) e. <_O(1) ) )

  proof
    wph
    cA
    cr
    wss
    #
    vx
    cA
    cB
    cmpt
    #
    clo1
    wcel
    #
    vx
    cA
    cC
    cmpt
    #
    clo1
    wcel
    #
    @2
    @1
    cdm
    #
    cr
    wss
    wph
    @0
    @1
    lo1dm
    wph
    @5
    cA
    cr
    wph
    vx
    @1
    cA
    cB
    cr
    @1
    eqid
    #
    lo1eq.1
    dmmptd
    sseq1d
    syl5ib
    @4
    @3
    cdm
    #
    cr
    wss
    wph
    @0
    @3
    lo1dm
    wph
    @7
    cA
    cr
    wph
    vx
    @3
    cA
    cC
    cr
    @3
    eqid
    #
    lo1eq.2
    dmmptd
    sseq1d
    syl5ib
    wph
    @0
    @2
    @4
    wb
    wph
    @0
    wa
    #
    @1
    cD
    cpnf
    cico
    co
    #
    cres
    #
    clo1
    wcel
    #
    @3
    @10
    cres
    #
    clo1
    wcel
    #
    @2
    @4
    wph
    @12
    @14
    wb
    @0
    wph
    @11
    @13
    clo1
    wph
    @1
    cA
    cres
    #
    @10
    cres
    #
    @3
    cA
    cres
    #
    @10
    cres
    #
    @11
    @13
    wph
    @1
    cA
    @10
    cin
    #
    cres
    #
    @3
    @19
    cres
    #
    @16
    @18
    wph
    vx
    @19
    cB
    cmpt
    #
    vx
    @19
    cC
    cmpt
    #
    @20
    @21
    wph
    vx
    @19
    cB
    cC
    wph
    vx
    cv
    #
    @19
    wcel
    #
    @24
    cA
    wcel
    #
    cD
    @24
    cle
    wbr
    #
    wa
    cB
    cC
    wceq
    wph
    @25
    wa
    #
    @26
    @27
    @28
    @26
    @24
    @10
    wcel
    #
    @28
    @25
    @26
    @29
    wa
    wph
    @25
    simpr
    @24
    cA
    @10
    elin
    sylib
    #
    simpld
    @28
    @24
    cr
    wcel
    #
    @27
    wph
    @25
    @29
    @31
    @27
    wa
    #
    @28
    @26
    @29
    @30
    simprd
    wph
    @29
    @32
    wph
    cD
    cr
    wcel
    #
    @29
    @32
    wb
    lo1eq.3
    cD
    @24
    elicopnf
    syl
    biimpa
    syldan
    simprd
    jca
    lo1eq.4
    syldan
    mpteq2dva
    @19
    cA
    wss
    #
    @20
    @22
    wceq
    cA
    @10
    inss1
    #
    vx
    cA
    @19
    cB
    resmpt
    ax-mp
    @34
    @21
    @23
    wceq
    @35
    vx
    cA
    @19
    cC
    resmpt
    ax-mp
    3eqtr4g
    @1
    cA
    @10
    resres
    @3
    cA
    @10
    resres
    3eqtr4g
    cA
    cA
    wss
    #
    @15
    @1
    wceq
    @16
    @11
    wceq
    cA
    ssid
    #
    vx
    cA
    cA
    cB
    resmpt
    @15
    @1
    @10
    reseq1
    mp2b
    @36
    @17
    @3
    wceq
    @18
    @13
    wceq
    @37
    vx
    cA
    cA
    cC
    resmpt
    @17
    @3
    @10
    reseq1
    mp2b
    3eqtr3g
    eleq1d
    adantr
    @9
    cA
    cD
    @1
    wph
    cA
    cr
    @1
    wf
    @0
    wph
    vx
    cA
    cB
    cr
    @1
    lo1eq.1
    @6
    fmptd
    adantr
    wph
    @0
    simpr
    #
    wph
    @33
    @0
    lo1eq.3
    adantr
    #
    lo1resb
    @9
    cA
    cD
    @3
    wph
    cA
    cr
    @3
    wf
    @0
    wph
    vx
    cA
    cC
    cr
    @3
    lo1eq.2
    @8
    fmptd
    adantr
    @38
    @39
    lo1resb
    3bitr4d
    ex
    pm5.21ndd
end
