include "crn.mm"
include "cfv.mm"
include "wf.mm"
include "wss.mm"
include "frn.mm"
include "syl.mm"
include "ccmn.mm"
include "wcel.mm"
include "wceq.mm"
include "cntzcmn.mm"
include "syl2anc.mm"
include "sseqtr4d.mm"

theorem cntzcmnf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cZ: class Z
  assume cntzcmnf.b: |- B = ( Base ` G )
  assume cntzcmnf.z: |- Z = ( Cntz ` G )
  assume cntzcmnf.g: |- ( ph -> G e. CMnd )
  assume cntzcmnf.f: |- ( ph -> F : A --> B )


  assert |- ( ph -> ran F C_ ( Z ` ran F ) )

  proof
    wph
    cF
    crn
    #
    cB
    @0
    cZ
    cfv
    #
    wph
    cA
    cB
    cF
    wf
    @0
    cB
    wss
    #
    cntzcmnf.f
    cA
    cB
    cF
    frn
    syl
    #
    wph
    cG
    ccmn
    wcel
    @2
    @1
    cB
    wceq
    cntzcmnf.g
    @3
    cB
    @0
    cG
    cZ
    cntzcmnf.b
    cntzcmnf.z
    cntzcmn
    syl2anc
    sseqtr4d
end
