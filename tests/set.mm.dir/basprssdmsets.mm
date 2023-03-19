include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cpr.mm"
include "cdm.mm"
include "csn.mm"
include "cun.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "wcel.mm"
include "wo.mm"
include "orcd.mm"
include "elun.mm"
include "sylibr.mm"
include "snidg.mm"
include "syl.mm"
include "olcd.mm"
include "prssd.mm"
include "cvv.mm"
include "wceq.mm"
include "cstr.mm"
include "wbr.mm"
include "structex.mm"
include "setsdm.mm"
include "syl2anc.mm"
include "sseqtr4d.mm"

theorem basprssdmsets
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cE: class E
  let cI: class I
  let cW: class W
  let cX: class X
  assume basprssdmsets.s: |- ( ph -> S Struct X )
  assume basprssdmsets.i: |- ( ph -> I e. U )
  assume basprssdmsets.w: |- ( ph -> E e. W )
  assume basprssdmsets.b: |- ( ph -> ( Base ` ndx ) e. dom S )


  assert |- ( ph -> { ( Base ` ndx ) , I } C_ dom ( S sSet <. I , E >. ) )

  proof
    wph
    cnx
    cbs
    cfv
    #
    cI
    cpr
    cS
    cdm
    #
    cI
    csn
    #
    cun
    #
    cS
    cI
    cE
    cop
    csts
    co
    cdm
    #
    wph
    @0
    cI
    @3
    wph
    @0
    @1
    wcel
    #
    @0
    @2
    wcel
    #
    wo
    @0
    @3
    wcel
    wph
    @5
    @6
    basprssdmsets.b
    orcd
    @0
    @1
    @2
    elun
    sylibr
    wph
    cI
    @1
    wcel
    #
    cI
    @2
    wcel
    #
    wo
    cI
    @3
    wcel
    wph
    @8
    @7
    wph
    cI
    cU
    wcel
    @8
    basprssdmsets.i
    cI
    cU
    snidg
    syl
    olcd
    cI
    @1
    @2
    elun
    sylibr
    prssd
    wph
    cS
    cvv
    wcel
    #
    cE
    cW
    wcel
    @4
    @3
    wceq
    wph
    cS
    cX
    cstr
    wbr
    @9
    basprssdmsets.s
    cS
    cX
    structex
    syl
    basprssdmsets.w
    cE
    cS
    cI
    cvv
    cW
    setsdm
    syl2anc
    sseqtr4d
end
