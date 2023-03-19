include "csalgen.mm"
include "cfv.mm"
include "eqid.mm"
include "salgenss.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "csalg.mm"
include "crab.mm"
include "cint.mm"
include "wral.mm"
include "wcel.mm"
include "simpl.mm"
include "elrabi.mm"
include "adantl.mm"
include "unieq.mm"
include "eqeq1d.mm"
include "sseq2.mm"
include "anbi12d.mm"
include "elrab.mm"
include "biimpi.mm"
include "simprld.mm"
include "simprrd.mm"
include "syl13anc.mm"
include "ralrimiva.mm"
include "ssint.mm"
include "sylibr.mm"
include "salgenval.mm"
include "syl.mm"
include "sseqtr4d.mm"
include "eqssd.mm"

theorem issalgend
  let wph: wff ph
  let vy: setvar y
  let cS: class S
  let cV: class V
  let cX: class X
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x
  assume issalgend.x: |- ( ph -> X e. V )
  assume issalgend.s: |- ( ph -> S e. SAlg )
  assume issalgend.u: |- ( ph -> U. S = U. X )
  assume issalgend.i: |- ( ph -> X C_ S )
  assume issalgend.a: |- ( ( ph /\ ( y e. SAlg /\ U. y = U. X /\ X C_ y ) ) -> S C_ y )

  disjoint S y
  disjoint X y
  disjoint ph y
  disjoint X s
  disjoint s y
  disjoint k x
  assert |- ( ph -> ( SalGen ` X ) = S )

  proof
    wph
    cX
    csalgen
    cfv
    #
    cS
    wph
    cS
    @0
    cV
    cX
    issalgend.x
    @0
    eqid
    issalgend.s
    issalgend.i
    issalgend.u
    salgenss
    wph
    cS
    vs
    cv
    #
    cuni
    #
    cX
    cuni
    #
    wceq
    #
    cX
    @1
    wss
    #
    wa
    #
    vs
    csalg
    crab
    #
    cint
    #
    @0
    wph
    cS
    vy
    cv
    #
    wss
    #
    vy
    @7
    wral
    cS
    @8
    wss
    wph
    @10
    vy
    @7
    wph
    @9
    @7
    wcel
    #
    wa
    wph
    @9
    csalg
    wcel
    #
    @9
    cuni
    #
    @3
    wceq
    #
    cX
    @9
    wss
    #
    @10
    wph
    @11
    simpl
    @11
    @12
    wph
    @6
    vs
    @9
    csalg
    elrabi
    adantl
    @11
    @14
    wph
    @11
    @12
    @14
    @15
    @11
    @12
    @14
    @15
    wa
    #
    wa
    @6
    @16
    vs
    @9
    csalg
    @1
    @9
    wceq
    #
    @4
    @14
    @5
    @15
    @17
    @2
    @13
    @3
    @1
    @9
    unieq
    eqeq1d
    @1
    @9
    cX
    sseq2
    anbi12d
    elrab
    biimpi
    #
    simprld
    adantl
    @11
    @15
    wph
    @11
    @12
    @14
    @15
    @18
    simprrd
    adantl
    issalgend.a
    syl13anc
    ralrimiva
    vy
    cS
    @7
    ssint
    sylibr
    wph
    cX
    cV
    wcel
    @0
    @8
    wceq
    issalgend.x
    cV
    cX
    vs
    salgenval
    syl
    sseqtr4d
    eqssd
end
