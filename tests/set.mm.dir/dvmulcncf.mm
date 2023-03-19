include "cmul.mm"
include "cof.mm"
include "co.mm"
include "cdv.mm"
include "caddc.mm"
include "cc.mm"
include "ccncf.mm"
include "wcel.mm"
include "wf.mm"
include "cdm.mm"
include "wceq.mm"
include "cncff.mm"
include "fdm.mm"
include "3syl.mm"
include "dvmulf.mm"
include "wss.mm"
include "cr.mm"
include "wi.mm"
include "wa.mm"
include "wo.mm"
include "ax-resscn.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "eqimss.mm"
include "pm3.2i.mm"
include "cpr.mm"
include "elpri.mm"
include "syl.mm"
include "pm3.44.mm"
include "mpsyl.mm"
include "dvbsss.mm"
include "syl6eqssr.mm"
include "dvcn.mm"
include "syl31anc.mm"
include "mulcncff.mm"
include "addcncff.mm"
include "eqeltrd.mm"

theorem dvmulcncf
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cG: class G
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume dvmulcncf.s: |- ( ph -> S e. { RR , CC } )
  assume dvmulcncf.f: |- ( ph -> F : X --> CC )
  assume dvmulcncf.g: |- ( ph -> G : X --> CC )
  assume dvmulcncf.fdv: |- ( ph -> ( S _D F ) e. ( X -cn-> CC ) )
  assume dvmulcncf.gdv: |- ( ph -> ( S _D G ) e. ( X -cn-> CC ) )


  assert |- ( ph -> ( S _D ( F oF x. G ) ) e. ( X -cn-> CC ) )

  proof
    wph
    cS
    cF
    cG
    cmul
    cof
    #
    co
    cdv
    co
    cS
    cF
    cdv
    co
    #
    cG
    @0
    co
    #
    cS
    cG
    cdv
    co
    #
    cF
    @0
    co
    #
    caddc
    cof
    co
    cX
    cc
    ccncf
    co
    #
    wph
    cS
    cF
    cG
    cX
    dvmulcncf.s
    dvmulcncf.f
    dvmulcncf.g
    wph
    @1
    @5
    wcel
    cX
    cc
    @1
    wf
    @1
    cdm
    #
    cX
    wceq
    #
    dvmulcncf.fdv
    cX
    cc
    @1
    cncff
    cX
    cc
    @1
    fdm
    3syl
    #
    wph
    @3
    @5
    wcel
    cX
    cc
    @3
    wf
    @3
    cdm
    cX
    wceq
    #
    dvmulcncf.gdv
    cX
    cc
    @3
    cncff
    cX
    cc
    @3
    fdm
    3syl
    #
    dvmulf
    wph
    @2
    @4
    cX
    wph
    @1
    cG
    cX
    dvmulcncf.fdv
    wph
    cS
    cc
    wss
    #
    cX
    cc
    cG
    wf
    cX
    cS
    wss
    #
    @9
    cG
    @5
    wcel
    cS
    cr
    wceq
    #
    @11
    wi
    #
    cS
    cc
    wceq
    #
    @11
    wi
    #
    wa
    wph
    @13
    @15
    wo
    #
    @11
    @14
    @16
    @13
    @11
    cr
    cc
    wss
    ax-resscn
    cS
    cr
    cc
    sseq1
    mpbiri
    cS
    cc
    eqimss
    pm3.2i
    wph
    cS
    cr
    cc
    cpr
    wcel
    @17
    dvmulcncf.s
    cS
    cr
    cc
    elpri
    syl
    @11
    @13
    @15
    pm3.44
    mpsyl
    #
    dvmulcncf.g
    wph
    cX
    @6
    cS
    @8
    cS
    cF
    dvbsss
    syl6eqssr
    #
    @10
    cX
    cS
    cG
    dvcn
    syl31anc
    mulcncff
    wph
    @3
    cF
    cX
    dvmulcncf.gdv
    wph
    @11
    cX
    cc
    cF
    wf
    @12
    @7
    cF
    @5
    wcel
    @18
    dvmulcncf.f
    @19
    @8
    cX
    cS
    cF
    dvcn
    syl31anc
    mulcncff
    addcncff
    eqeltrd
end
