include "cmpt.mm"
include "cres.mm"
include "ccn.mm"
include "co.mm"
include "resmptd.mm"
include "crest.mm"
include "wcel.mm"
include "cuni.mm"
include "wss.mm"
include "ctopon.mm"
include "cfv.mm"
include "wceq.mm"
include "toponuni.mm"
include "syl.mm"
include "sseqtrd.mm"
include "eqid.mm"
include "cnrest.mm"
include "syl2anc.mm"
include "oveq1i.mm"
include "syl6eleqr.mm"
include "eqeltrrd.mm"

theorem cnmpt1res
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let cW: class W
  let cZ: class Z
  assume cnmpt1res.2: |- K = ( J |`t Y )
  assume cnmpt1res.3: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmpt1res.5: |- ( ph -> Y C_ X )
  assume cnmpt1res.6: |- ( ph -> ( x e. X |-> A ) e. ( J Cn L ) )

  disjoint X x
  disjoint Y x
  disjoint x y
  disjoint W x
  disjoint W y
  disjoint X y
  disjoint Y y
  disjoint Z x
  disjoint Z y
  assert |- ( ph -> ( x e. Y |-> A ) e. ( K Cn L ) )

  proof
    wph
    vx
    cX
    cA
    cmpt
    #
    cY
    cres
    #
    vx
    cY
    cA
    cmpt
    cK
    cL
    ccn
    co
    #
    wph
    vx
    cX
    cY
    cA
    cnmpt1res.5
    resmptd
    wph
    @1
    cJ
    cY
    crest
    co
    #
    cL
    ccn
    co
    #
    @2
    wph
    @0
    cJ
    cL
    ccn
    co
    wcel
    cY
    cJ
    cuni
    #
    wss
    @1
    @4
    wcel
    cnmpt1res.6
    wph
    cY
    cX
    @5
    cnmpt1res.5
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    cX
    @5
    wceq
    cnmpt1res.3
    cX
    cJ
    toponuni
    syl
    sseqtrd
    cY
    @0
    cJ
    cL
    @5
    @5
    eqid
    cnrest
    syl2anc
    cK
    @3
    cL
    ccn
    cnmpt1res.2
    oveq1i
    syl6eleqr
    eqeltrrd
end
