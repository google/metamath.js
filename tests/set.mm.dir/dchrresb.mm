include "cres.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "cbs.mm"
include "wfn.mm"
include "wb.mm"
include "cc.mm"
include "wf.mm"
include "eqid.mm"
include "dchrf.mm"
include "ffn.mm"
include "syl.mm"
include "wa.mm"
include "wss.mm"
include "unitss.mm"
include "fvreseq.mm"
include "mpan2.mm"
include "syl2anc.mm"
include "dchreq.mm"
include "bitr4d.mm"

theorem dchrresb
  let wph: wff ph
  let cD: class D
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vk: setvar k
  assume dchrresb.g: |- G = ( DChr ` N )
  assume dchrresb.z: |- Z = ( Z/nZ ` N )
  assume dchrresb.b: |- D = ( Base ` G )
  assume dchrresb.u: |- U = ( Unit ` Z )
  assume dchrresb.x: |- ( ph -> X e. D )
  assume dchrresb.Y: |- ( ph -> Y e. D )


  assert |- ( ph -> ( ( X |` U ) = ( Y |` U ) <-> X = Y ) )

  proof
    wph
    cX
    cU
    cres
    cY
    cU
    cres
    wceq
    #
    vk
    cv
    #
    cX
    cfv
    @1
    cY
    cfv
    wceq
    vk
    cU
    wral
    #
    cX
    cY
    wceq
    wph
    cX
    cZ
    cbs
    cfv
    #
    wfn
    #
    cY
    @3
    wfn
    #
    @0
    @2
    wb
    #
    wph
    @3
    cc
    cX
    wf
    @4
    wph
    @3
    cD
    cG
    cN
    cX
    cZ
    dchrresb.g
    dchrresb.z
    dchrresb.b
    @3
    eqid
    #
    dchrresb.x
    dchrf
    @3
    cc
    cX
    ffn
    syl
    wph
    @3
    cc
    cY
    wf
    @5
    wph
    @3
    cD
    cG
    cN
    cY
    cZ
    dchrresb.g
    dchrresb.z
    dchrresb.b
    @7
    dchrresb.Y
    dchrf
    @3
    cc
    cY
    ffn
    syl
    @4
    @5
    wa
    cU
    @3
    wss
    @6
    @3
    cZ
    cU
    @7
    dchrresb.u
    unitss
    vk
    @3
    cU
    cX
    cY
    fvreseq
    mpan2
    syl2anc
    wph
    cD
    cU
    vk
    cG
    cN
    cX
    cY
    cZ
    dchrresb.g
    dchrresb.z
    dchrresb.b
    dchrresb.u
    dchrresb.x
    dchrresb.Y
    dchreq
    bitr4d
end
