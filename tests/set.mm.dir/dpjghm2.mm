include "cfv.mm"
include "cdprd.mm"
include "co.mm"
include "cress.mm"
include "cghm.mm"
include "wcel.mm"
include "dpjghm.mm"
include "csubg.mm"
include "crn.mm"
include "wss.mm"
include "wb.mm"
include "dprdf2.mm"
include "ffvelrnd.mm"
include "wf.mm"
include "dpjf.mm"
include "frn.mm"
include "syl.mm"
include "eqid.mm"
include "resghm2b.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem dpjghm2
  let wph: wff ph
  let cP: class P
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
  let cC: class C
  let cQ: class Q
  let cW: class W
  let cA: class A
  let cY: class Y
  assume dpjfval.1: |- ( ph -> G dom DProd S )
  assume dpjfval.2: |- ( ph -> dom S = I )
  assume dpjfval.p: |- P = ( G dProj S )
  assume dpjlid.3: |- ( ph -> X e. I )


  assert |- ( ph -> ( P ` X ) e. ( ( G |`s ( G DProd S ) ) GrpHom ( G |`s ( S ` X ) ) ) )

  proof
    wph
    cX
    cP
    cfv
    #
    cG
    cG
    cS
    cdprd
    co
    #
    cress
    co
    #
    cG
    cghm
    co
    wcel
    #
    @0
    @2
    cG
    cX
    cS
    cfv
    #
    cress
    co
    #
    cghm
    co
    wcel
    #
    wph
    cP
    cS
    cG
    cI
    cX
    dpjfval.1
    dpjfval.2
    dpjfval.p
    dpjlid.3
    dpjghm
    wph
    @4
    cG
    csubg
    cfv
    #
    wcel
    @0
    crn
    @4
    wss
    #
    @3
    @6
    wb
    wph
    cI
    @7
    cX
    cS
    wph
    cS
    cG
    cI
    dpjfval.1
    dpjfval.2
    dprdf2
    dpjlid.3
    ffvelrnd
    wph
    @1
    @4
    @0
    wf
    @8
    wph
    cP
    cS
    cG
    cI
    cX
    dpjfval.1
    dpjfval.2
    dpjfval.p
    dpjlid.3
    dpjf
    @1
    @4
    @0
    frn
    syl
    @2
    cG
    @5
    @0
    @4
    @5
    eqid
    resghm2b
    syl2anc
    mpbid
end
