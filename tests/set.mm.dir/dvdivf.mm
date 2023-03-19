include "cv.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "cdv.mm"
include "cmul.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "cof.mm"
include "cc.mm"
include "ffvelrnda.mm"
include "cdm.mm"
include "wf.mm"
include "cr.mm"
include "cpr.mm"
include "wcel.mm"
include "dvfg.mm"
include "syl.mm"
include "feq2d.mm"
include "mpbid.mm"
include "feqmptd.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "dvmptdiv.mm"
include "cvv.mm"
include "ovex.mm"
include "dmex.mm"
include "syl6eqelr.mm"
include "offval2.mm"
include "wa.mm"
include "ovexd.mm"
include "eldifad.mm"
include "sqcld.mm"
include "mulcld.mm"
include "sqvald.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "3eqtr4d.mm"

theorem dvdivf
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vk: setvar k
  assume dvdivf.s: |- ( ph -> S e. { RR , CC } )
  assume dvdivf.f: |- ( ph -> F : X --> CC )
  assume dvdivf.g: |- ( ph -> G : X --> ( CC \ { 0 } ) )
  assume dvdivf.fdv: |- ( ph -> dom ( S _D F ) = X )
  assume dvdivf.gdv: |- ( ph -> dom ( S _D G ) = X )


  assert |- ( ph -> ( S _D ( F oF / G ) ) = ( ( ( ( S _D F ) oF x. G ) oF - ( ( S _D G ) oF x. F ) ) oF / ( G oF x. G ) ) )

  proof
    wph
    cS
    vx
    cX
    vx
    cv
    #
    cF
    cfv
    #
    @0
    cG
    cfv
    #
    cdiv
    co
    cmpt
    #
    cdv
    co
    vx
    cX
    @0
    cS
    cF
    cdv
    co
    #
    cfv
    #
    @2
    cmul
    co
    #
    @0
    cS
    cG
    cdv
    co
    #
    cfv
    #
    @1
    cmul
    co
    #
    cmin
    co
    #
    @2
    c2
    cexp
    co
    #
    cdiv
    co
    cmpt
    cS
    cF
    cG
    cdiv
    cof
    #
    co
    #
    cdv
    co
    @4
    cG
    cmul
    cof
    #
    co
    #
    @7
    cF
    @14
    co
    #
    cmin
    cof
    co
    #
    cG
    cG
    @14
    co
    #
    @12
    co
    wph
    vx
    @1
    @5
    @2
    @8
    cS
    cc
    cX
    dvdivf.s
    wph
    cX
    cc
    @0
    cF
    dvdivf.f
    ffvelrnda
    #
    wph
    cX
    cc
    @0
    @4
    wph
    @4
    cdm
    #
    cc
    @4
    wf
    #
    cX
    cc
    @4
    wf
    wph
    cS
    cr
    cc
    cpr
    wcel
    #
    @21
    dvdivf.s
    cS
    cF
    dvfg
    syl
    wph
    @20
    cX
    cc
    @4
    dvdivf.fdv
    feq2d
    mpbid
    #
    ffvelrnda
    #
    wph
    @4
    cS
    vx
    cX
    @1
    cmpt
    #
    cdv
    co
    vx
    cX
    @5
    cmpt
    wph
    cF
    @25
    cS
    cdv
    wph
    vx
    cX
    cc
    cF
    dvdivf.f
    feqmptd
    #
    oveq2d
    wph
    vx
    cX
    cc
    @4
    @23
    feqmptd
    #
    eqtr3d
    wph
    cX
    cc
    cc0
    csn
    #
    cdif
    #
    @0
    cG
    dvdivf.g
    ffvelrnda
    #
    wph
    cX
    cc
    @0
    @7
    wph
    @7
    cdm
    #
    cc
    @7
    wf
    #
    cX
    cc
    @7
    wf
    wph
    @22
    @32
    dvdivf.s
    cS
    cG
    dvfg
    syl
    wph
    @31
    cX
    cc
    @7
    dvdivf.gdv
    feq2d
    mpbid
    #
    ffvelrnda
    #
    wph
    @7
    cS
    vx
    cX
    @2
    cmpt
    #
    cdv
    co
    vx
    cX
    @8
    cmpt
    wph
    cG
    @35
    cS
    cdv
    wph
    vx
    cX
    @29
    cG
    dvdivf.g
    feqmptd
    #
    oveq2d
    wph
    vx
    cX
    cc
    @7
    @33
    feqmptd
    #
    eqtr3d
    dvmptdiv
    wph
    @13
    @3
    cS
    cdv
    wph
    vx
    cX
    @1
    @2
    cdiv
    cF
    cG
    cvv
    cc
    @29
    wph
    cX
    @20
    cvv
    dvdivf.fdv
    @4
    cS
    cF
    cdv
    ovex
    dmex
    syl6eqelr
    #
    @19
    @30
    @26
    @36
    offval2
    oveq2d
    wph
    vx
    cX
    @10
    @11
    cdiv
    @17
    @18
    cvv
    cvv
    cc
    @38
    wph
    @0
    cX
    wcel
    wa
    #
    @6
    @9
    cmin
    ovexd
    @39
    @2
    @39
    @2
    cc
    @28
    @30
    eldifad
    #
    sqcld
    wph
    vx
    cX
    @6
    @9
    cmin
    @15
    @16
    cvv
    cc
    cc
    @38
    @39
    @5
    @2
    @24
    @40
    mulcld
    @39
    @8
    @1
    @34
    @19
    mulcld
    wph
    vx
    cX
    @5
    @2
    cmul
    @4
    cG
    cvv
    cc
    cc
    @38
    @24
    @40
    @27
    @36
    offval2
    wph
    vx
    cX
    @8
    @1
    cmul
    @7
    cF
    cvv
    cc
    cc
    @38
    @34
    @19
    @37
    @26
    offval2
    offval2
    wph
    @18
    vx
    cX
    @2
    @2
    cmul
    co
    #
    cmpt
    vx
    cX
    @11
    cmpt
    wph
    vx
    cX
    @2
    @2
    cmul
    cG
    cG
    cvv
    @29
    @29
    @38
    @30
    @30
    @36
    @36
    offval2
    wph
    vx
    cX
    @11
    @41
    @39
    @2
    @40
    sqvald
    mpteq2dva
    eqtr4d
    offval2
    3eqtr4d
end
