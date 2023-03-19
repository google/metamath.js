include "cr.mm"
include "cicc.mm"
include "co.mm"
include "cres.mm"
include "cdv.mm"
include "cmpt.mm"
include "cioo.mm"
include "cc.mm"
include "reseq1i.mm"
include "iccssred.mm"
include "wss.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "sstrd.mm"
include "resmptd.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "cnt.mm"
include "resabs1d.mm"
include "eqcomd.mm"
include "wf.mm"
include "wceq.mm"
include "fmptd.mm"
include "fssresd.mm"
include "ssid.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "tgioo2.mm"
include "dvres.mm"
include "syl22anc.mm"
include "cpr.mm"
include "wcel.mm"
include "cdm.mm"
include "reelprrecn.mm"
include "dmeqd.mm"
include "wral.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "syl.mm"
include "eqtr2d.mm"
include "sseqtrd.mm"
include "dvres3.mm"
include "iccntr.mm"
include "syl2anc.mm"
include "reseq12d.mm"
include "ioossre.mm"
include "resabs1.mm"
include "mp1i.mm"
include "reseq1d.mm"
include "ioosscn.mm"
include "resmpt.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "eqtr3d.mm"

theorem dvmptresicc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let vk: setvar k
  assume dvmptresicc.f: |- F = ( x e. CC |-> A )
  assume dvmptresicc.a: |- ( ( ph /\ x e. CC ) -> A e. CC )
  assume dvmptresicc.fdv: |- ( ph -> ( CC _D F ) = ( x e. CC |-> B ) )
  assume dvmptresicc.b: |- ( ( ph /\ x e. CC ) -> B e. CC )
  assume dvmptresicc.c: |- ( ph -> C e. RR )
  assume dvmptresicc.d: |- ( ph -> D e. RR )

  disjoint C x
  disjoint D x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( RR _D ( x e. ( C [,] D ) |-> A ) ) = ( x e. ( C (,) D ) |-> B ) )

  proof
    wph
    cr
    cF
    cC
    cD
    cicc
    co
    #
    cres
    #
    cdv
    co
    #
    cr
    vx
    @0
    cA
    cmpt
    #
    cdv
    co
    vx
    cC
    cD
    cioo
    co
    #
    cB
    cmpt
    #
    wph
    @1
    @3
    cr
    cdv
    wph
    @1
    vx
    cc
    cA
    cmpt
    #
    @0
    cres
    @3
    cF
    @6
    @0
    dvmptresicc.f
    reseq1i
    wph
    vx
    cc
    @0
    cA
    wph
    @0
    cr
    cc
    wph
    cC
    cD
    dvmptresicc.c
    dvmptresicc.d
    iccssred
    #
    cr
    cc
    wss
    #
    wph
    ax-resscn
    a1i
    #
    sstrd
    resmptd
    syl5eq
    oveq2d
    wph
    @2
    cr
    cF
    cr
    cres
    #
    @0
    cres
    #
    cdv
    co
    #
    cr
    @10
    cdv
    co
    #
    @0
    cioo
    crn
    ctg
    cfv
    #
    cnt
    cfv
    cfv
    #
    cres
    #
    @5
    wph
    @1
    @11
    cr
    cdv
    wph
    @11
    @1
    wph
    cF
    @0
    cr
    @7
    resabs1d
    eqcomd
    oveq2d
    wph
    @8
    cr
    cc
    @10
    wf
    cr
    cr
    wss
    #
    @0
    cr
    wss
    @12
    @16
    wceq
    @9
    wph
    cc
    cc
    cr
    cF
    wph
    vx
    cc
    cA
    cc
    cF
    dvmptresicc.a
    dvmptresicc.f
    fmptd
    #
    @9
    fssresd
    @17
    wph
    cr
    ssid
    a1i
    @7
    cr
    @0
    cr
    @14
    @10
    ccnfld
    ctopn
    cfv
    #
    @19
    eqid
    #
    @19
    @20
    tgioo2
    dvres
    syl22anc
    wph
    @16
    cc
    cF
    cdv
    co
    #
    cr
    cres
    #
    @4
    cres
    #
    @21
    @4
    cres
    #
    @5
    wph
    @13
    @22
    @15
    @4
    wph
    cr
    cr
    cc
    cpr
    wcel
    #
    cc
    cc
    cF
    wf
    cc
    cc
    wss
    #
    cr
    @21
    cdm
    #
    wss
    @13
    @22
    wceq
    @25
    wph
    reelprrecn
    a1i
    @18
    @26
    wph
    cc
    ssid
    a1i
    wph
    cr
    cc
    @27
    @9
    wph
    @27
    vx
    cc
    cB
    cmpt
    #
    cdm
    #
    cc
    wph
    @21
    @28
    dvmptresicc.fdv
    dmeqd
    wph
    cB
    cc
    wcel
    #
    vx
    cc
    wral
    @29
    cc
    wceq
    wph
    @30
    vx
    cc
    dvmptresicc.b
    ralrimiva
    vx
    cc
    cB
    cc
    dmmptg
    syl
    eqtr2d
    sseqtrd
    cc
    cr
    cF
    dvres3
    syl22anc
    wph
    cC
    cr
    wcel
    cD
    cr
    wcel
    @15
    @4
    wceq
    dvmptresicc.c
    dvmptresicc.d
    cC
    cD
    iccntr
    syl2anc
    reseq12d
    @4
    cr
    wss
    @23
    @24
    wceq
    wph
    cC
    cD
    ioossre
    @21
    @4
    cr
    resabs1
    mp1i
    wph
    @24
    @28
    @4
    cres
    #
    @5
    wph
    @21
    @28
    @4
    dvmptresicc.fdv
    reseq1d
    @4
    cc
    wss
    @31
    @5
    wceq
    wph
    cC
    cD
    ioosscn
    vx
    cc
    @4
    cB
    resmpt
    mp1i
    eqtrd
    3eqtrd
    3eqtrd
    eqtr3d
end
