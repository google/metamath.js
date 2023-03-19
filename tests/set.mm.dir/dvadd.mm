include "caddc.mm"
include "cof.mm"
include "co.mm"
include "cdv.mm"
include "wfun.mm"
include "cfv.mm"
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
include "dvaddbr.mm"
include "funbrfv.mm"
include "sylc.mm"

theorem dvadd
  let wph: wff ph
  let cC: class C
  let cS: class S
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  let cJ: class J
  let vx: setvar x
  let cK: class K
  let cL: class L
  assume dvadd.f: |- ( ph -> F : X --> CC )
  assume dvadd.x: |- ( ph -> X C_ S )
  assume dvadd.g: |- ( ph -> G : Y --> CC )
  assume dvadd.y: |- ( ph -> Y C_ S )
  assume dvadd.s: |- ( ph -> S e. { RR , CC } )
  assume dvadd.df: |- ( ph -> C e. dom ( S _D F ) )
  assume dvadd.dg: |- ( ph -> C e. dom ( S _D G ) )


  assert |- ( ph -> ( ( S _D ( F oF + G ) ) ` C ) = ( ( ( S _D F ) ` C ) + ( ( S _D G ) ` C ) ) )

  proof
    wph
    cS
    cF
    cG
    caddc
    cof
    co
    #
    cdv
    co
    #
    wfun
    #
    cC
    cC
    cS
    cF
    cdv
    co
    #
    cfv
    #
    cC
    cS
    cG
    cdv
    co
    #
    cfv
    #
    caddc
    co
    #
    @1
    wbr
    cC
    @1
    cfv
    @7
    wceq
    wph
    cS
    cr
    cc
    cpr
    wcel
    #
    @1
    cdm
    #
    cc
    @1
    wf
    @2
    dvadd.s
    cS
    @0
    dvfg
    @9
    cc
    @1
    ffun
    3syl
    wph
    cC
    cS
    cF
    cG
    ccnfld
    ctopn
    cfv
    #
    @4
    @6
    cvv
    cX
    cY
    dvadd.f
    dvadd.x
    dvadd.g
    dvadd.y
    wph
    @8
    cS
    cc
    wss
    dvadd.s
    cS
    recnprss
    syl
    wph
    cC
    @3
    fvexd
    wph
    cC
    @5
    fvexd
    wph
    cC
    @3
    cdm
    #
    wcel
    #
    cC
    @4
    @3
    wbr
    #
    dvadd.df
    wph
    @8
    @11
    cc
    @3
    wf
    @3
    wfun
    @12
    @13
    wb
    dvadd.s
    cS
    cF
    dvfg
    @11
    cc
    @3
    ffun
    cC
    @3
    funfvbrb
    4syl
    mpbid
    wph
    cC
    @5
    cdm
    #
    wcel
    #
    cC
    @6
    @5
    wbr
    #
    dvadd.dg
    wph
    @8
    @14
    cc
    @5
    wf
    @5
    wfun
    @15
    @16
    wb
    dvadd.s
    cS
    cG
    dvfg
    @14
    cc
    @5
    ffun
    cC
    @5
    funfvbrb
    4syl
    mpbid
    @10
    eqid
    dvaddbr
    cC
    @7
    @1
    funbrfv
    sylc
end
