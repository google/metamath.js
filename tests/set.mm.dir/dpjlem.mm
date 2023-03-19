include "csn.mm"
include "cres.mm"
include "cdprd.mm"
include "co.mm"
include "cfv.mm"
include "cop.mm"
include "wfn.mm"
include "wcel.mm"
include "wceq.mm"
include "csubg.mm"
include "wf.mm"
include "dprdf2.mm"
include "ffn.mm"
include "syl.mm"
include "fnressn.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "cdm.mm"
include "wbr.mm"
include "wa.mm"
include "ffvelrnd.mm"
include "dprdsn.mm"
include "simprd.mm"
include "eqtrd.mm"

theorem dpjlem
  let wph: wff ph
  let cS: class S
  let cG: class G
  let cI: class I
  let cX: class X
  let vh: setvar h
  let vk: setvar k
  let vx: setvar x
  let c.0: class .0.
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vs: setvar s
  let cP: class P
  let cC: class C
  let cQ: class Q
  let cW: class W
  let cA: class A
  let cY: class Y
  assume dpjfval.1: |- ( ph -> G dom DProd S )
  assume dpjfval.2: |- ( ph -> dom S = I )
  assume dpjlem.3: |- ( ph -> X e. I )


  assert |- ( ph -> ( G DProd ( S |` { X } ) ) = ( S ` X ) )

  proof
    wph
    cG
    cS
    cX
    csn
    cres
    #
    cdprd
    co
    cG
    cX
    cX
    cS
    cfv
    #
    cop
    csn
    #
    cdprd
    co
    #
    @1
    wph
    @0
    @2
    cG
    cdprd
    wph
    cS
    cI
    wfn
    #
    cX
    cI
    wcel
    #
    @0
    @2
    wceq
    wph
    cI
    cG
    csubg
    cfv
    #
    cS
    wf
    @4
    wph
    cS
    cG
    cI
    dpjfval.1
    dpjfval.2
    dprdf2
    #
    cI
    @6
    cS
    ffn
    syl
    dpjlem.3
    cI
    cX
    cS
    fnressn
    syl2anc
    oveq2d
    wph
    cG
    @2
    cdprd
    cdm
    wbr
    #
    @3
    @1
    wceq
    #
    wph
    @5
    @1
    @6
    wcel
    @8
    @9
    wa
    dpjlem.3
    wph
    cI
    @6
    cX
    cS
    @7
    dpjlem.3
    ffvelrnd
    cX
    @1
    cG
    cI
    dprdsn
    syl2anc
    simprd
    eqtrd
end
