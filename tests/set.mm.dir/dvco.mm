include "ccom.mm"
include "cdv.mm"
include "co.mm"
include "wfun.mm"
include "cfv.mm"
include "cmul.mm"
include "wbr.mm"
include "wceq.mm"
include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "cdm.mm"
include "wf.mm"
include "dvfg.mm"
include "ffun.mm"
include "3syl.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cvv.mm"
include "wss.mm"
include "recnprss.mm"
include "syl.mm"
include "fvexd.mm"
include "wb.mm"
include "funfvbrb.mm"
include "4syl.mm"
include "mpbid.mm"
include "eqid.mm"
include "dvcobr.mm"
include "funbrfv.mm"
include "sylc.mm"

theorem dvco
  let wph: wff ph
  let cC: class C
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  let cJ: class J
  let cL: class L
  let cK: class K
  assume dvco.f: |- ( ph -> F : X --> CC )
  assume dvco.x: |- ( ph -> X C_ S )
  assume dvco.g: |- ( ph -> G : Y --> X )
  assume dvco.y: |- ( ph -> Y C_ T )
  assume dvco.s: |- ( ph -> S e. { RR , CC } )
  assume dvco.t: |- ( ph -> T e. { RR , CC } )
  assume dvco.df: |- ( ph -> ( G ` C ) e. dom ( S _D F ) )
  assume dvco.dg: |- ( ph -> C e. dom ( T _D G ) )


  assert |- ( ph -> ( ( T _D ( F o. G ) ) ` C ) = ( ( ( S _D F ) ` ( G ` C ) ) x. ( ( T _D G ) ` C ) ) )

  proof
    wph
    cT
    cF
    cG
    ccom
    #
    cdv
    co
    #
    wfun
    #
    cC
    cC
    cG
    cfv
    #
    cS
    cF
    cdv
    co
    #
    cfv
    #
    cC
    cT
    cG
    cdv
    co
    #
    cfv
    #
    cmul
    co
    #
    @1
    wbr
    cC
    @1
    cfv
    @8
    wceq
    wph
    cT
    cr
    cc
    cpr
    #
    wcel
    #
    @1
    cdm
    #
    cc
    @1
    wf
    @2
    dvco.t
    cT
    @0
    dvfg
    @11
    cc
    @1
    ffun
    3syl
    wph
    cC
    cS
    cT
    cF
    cG
    ccnfld
    ctopn
    cfv
    #
    @5
    @7
    cvv
    cX
    cY
    dvco.f
    dvco.x
    dvco.g
    dvco.y
    wph
    cS
    @9
    wcel
    #
    cS
    cc
    wss
    dvco.s
    cS
    recnprss
    syl
    wph
    @10
    cT
    cc
    wss
    dvco.t
    cT
    recnprss
    syl
    wph
    @3
    @4
    fvexd
    wph
    cC
    @6
    fvexd
    wph
    @3
    @4
    cdm
    #
    wcel
    #
    @3
    @5
    @4
    wbr
    #
    dvco.df
    wph
    @13
    @14
    cc
    @4
    wf
    @4
    wfun
    @15
    @16
    wb
    dvco.s
    cS
    cF
    dvfg
    @14
    cc
    @4
    ffun
    @3
    @4
    funfvbrb
    4syl
    mpbid
    wph
    cC
    @6
    cdm
    #
    wcel
    #
    cC
    @7
    @6
    wbr
    #
    dvco.dg
    wph
    @10
    @17
    cc
    @6
    wf
    @6
    wfun
    @18
    @19
    wb
    dvco.t
    cT
    cG
    dvfg
    @17
    cc
    @6
    ffun
    cC
    @6
    funfvbrb
    4syl
    mpbid
    @12
    eqid
    dvcobr
    cC
    @8
    @1
    funbrfv
    sylc
end
