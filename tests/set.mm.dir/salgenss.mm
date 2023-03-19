include "cv.mm"
include "cuni.mm"
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
include "jca.mm"
include "unieq.mm"
include "eqeq1d.mm"
include "sseq2.mm"
include "anbi12d.mm"
include "elrab.mm"
include "sylibr.mm"
include "intss1.mm"
include "eqsstrd.mm"

theorem salgenss
  let wph: wff ph
  let cS: class S
  let cG: class G
  let cV: class V
  let cX: class X
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x
  assume salgenss.x: |- ( ph -> X e. V )
  assume salgenss.g: |- G = ( SalGen ` X )
  assume salgenss.s: |- ( ph -> S e. SAlg )
  assume salgenss.i: |- ( ph -> X C_ S )
  assume salgenss.u: |- ( ph -> U. S = U. X )


  assert |- ( ph -> G C_ S )

  proof
    wph
    cG
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
    cS
    wph
    cG
    cX
    csalgen
    cfv
    #
    @7
    cG
    @8
    wceq
    wph
    salgenss.g
    a1i
    wph
    cX
    cV
    wcel
    @8
    @7
    wceq
    salgenss.x
    cV
    cX
    vs
    salgenval
    syl
    eqtrd
    wph
    cS
    @6
    wcel
    #
    @7
    cS
    wss
    wph
    cS
    csalg
    wcel
    #
    cS
    cuni
    #
    @2
    wceq
    #
    cX
    cS
    wss
    #
    wa
    #
    wa
    @9
    wph
    @10
    @14
    salgenss.s
    wph
    @12
    @13
    salgenss.u
    salgenss.i
    jca
    jca
    @5
    @14
    vs
    cS
    csalg
    @0
    cS
    wceq
    #
    @3
    @12
    @4
    @13
    @15
    @1
    @11
    @2
    @0
    cS
    unieq
    eqeq1d
    @0
    cS
    cX
    sseq2
    anbi12d
    elrab
    sylibr
    cS
    @6
    intss1
    syl
    eqsstrd
end
