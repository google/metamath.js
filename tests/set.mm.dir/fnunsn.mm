include "cop.mm"
include "csn.mm"
include "cun.mm"
include "wfn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "fnsng.mm"
include "syl2anc.mm"
include "wn.mm"
include "disjsn.mm"
include "sylibr.mm"
include "fnun.mm"
include "syl21anc.mm"
include "fneq1i.mm"
include "fneq2i.mm"
include "bitri.mm"

theorem fnunsn
  let wph: wff ph
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  assume fnunop.x: |- ( ph -> X e. _V )
  assume fnunop.y: |- ( ph -> Y e. _V )
  assume fnunop.f: |- ( ph -> F Fn D )
  assume fnunop.g: |- G = ( F u. { <. X , Y >. } )
  assume fnunop.e: |- E = ( D u. { X } )
  assume fnunop.d: |- ( ph -> -. X e. D )


  assert |- ( ph -> G Fn E )

  proof
    wph
    cF
    cX
    cY
    cop
    csn
    #
    cun
    #
    cD
    cX
    csn
    #
    cun
    #
    wfn
    #
    cG
    cE
    wfn
    #
    wph
    cF
    cD
    wfn
    @0
    @2
    wfn
    #
    cD
    @2
    cin
    c0
    wceq
    #
    @4
    fnunop.f
    wph
    cX
    cvv
    wcel
    cY
    cvv
    wcel
    @6
    fnunop.x
    fnunop.y
    cX
    cY
    cvv
    cvv
    fnsng
    syl2anc
    wph
    cX
    cD
    wcel
    wn
    @7
    fnunop.d
    cD
    cX
    disjsn
    sylibr
    cD
    @2
    cF
    @0
    fnun
    syl21anc
    @5
    @1
    cE
    wfn
    @4
    cE
    cG
    @1
    fnunop.g
    fneq1i
    cE
    @3
    @1
    fnunop.e
    fneq2i
    bitri
    sylibr
end
