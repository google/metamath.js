include "cuni.mm"
include "cv.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "csalg.mm"
include "crab.mm"
include "cint.mm"
include "csalgen.mm"
include "cfv.mm"
include "a1i.mm"
include "wcel.mm"
include "salgenval.mm"
include "syl.mm"
include "eqtrd.mm"
include "unieqd.mm"
include "ssrab2.mm"
include "c0.mm"
include "wne.mm"
include "salgenn0.mm"
include "unieq.mm"
include "eqeq1d.mm"
include "sseq2.mm"
include "anbi12d.mm"
include "elrab.mm"
include "biimpi.mm"
include "simprld.mm"
include "eqcomi.mm"
include "adantl.mm"
include "intsaluni.mm"

theorem salgenuni
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cV: class V
  let cX: class X
  let vt: setvar t
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x
  assume salgenuni.x: |- ( ph -> X e. V )
  assume salgenuni.s: |- S = ( SalGen ` X )
  assume salgenuni.u: |- U = U. X


  assert |- ( ph -> U. S = U )

  proof
    wph
    cS
    cuni
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
    @0
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
    cuni
    cU
    wph
    cS
    @7
    wph
    cS
    cX
    csalgen
    cfv
    #
    @7
    cS
    @8
    wceq
    wph
    salgenuni.s
    a1i
    wph
    cX
    cV
    wcel
    #
    @8
    @7
    wceq
    salgenuni.x
    cV
    cX
    vs
    salgenval
    syl
    eqtrd
    unieqd
    wph
    @6
    cU
    vt
    @6
    csalg
    wss
    wph
    @5
    vs
    csalg
    ssrab2
    a1i
    wph
    @9
    @6
    c0
    wne
    salgenuni.x
    cV
    cX
    vs
    salgenn0
    syl
    vt
    cv
    #
    @6
    wcel
    #
    @10
    cuni
    #
    cU
    wceq
    wph
    @11
    @12
    @2
    cU
    @11
    @10
    csalg
    wcel
    #
    @12
    @2
    wceq
    #
    cX
    @10
    wss
    #
    @11
    @13
    @14
    @15
    wa
    #
    wa
    @5
    @16
    vs
    @10
    csalg
    @0
    @10
    wceq
    #
    @3
    @14
    @4
    @15
    @17
    @1
    @12
    @2
    @0
    @10
    unieq
    eqeq1d
    @0
    @10
    cX
    sseq2
    anbi12d
    elrab
    biimpi
    simprld
    @2
    cU
    wceq
    @11
    cU
    @2
    salgenuni.u
    eqcomi
    a1i
    eqtrd
    adantl
    intsaluni
    eqtrd
end
