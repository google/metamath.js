include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "cbs.mm"
include "cdif.mm"
include "wa.mm"
include "wfn.mm"
include "wb.mm"
include "cc.mm"
include "wf.mm"
include "eqid.mm"
include "dchrf.mm"
include "ffn.mm"
include "syl.mm"
include "eqfnfv.mm"
include "syl2anc.mm"
include "cun.mm"
include "wss.mm"
include "unitss.mm"
include "undif.mm"
include "mpbi.mm"
include "raleqi.mm"
include "ralunb.mm"
include "bitr3i.mm"
include "syl6bb.mm"
include "wcel.mm"
include "cc0.mm"
include "wn.mm"
include "eldif.mm"
include "wne.mm"
include "adantr.mm"
include "simpr.mm"
include "dchrn0.mm"
include "biimpd.mm"
include "necon1bd.mm"
include "impr.mm"
include "sylan2b.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "biantrud.mm"
include "bitr4d.mm"

theorem dchreq
  let wph: wff ph
  let cD: class D
  let cU: class U
  let vk: setvar k
  let cG: class G
  let cN: class N
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume dchrresb.g: |- G = ( DChr ` N )
  assume dchrresb.z: |- Z = ( Z/nZ ` N )
  assume dchrresb.b: |- D = ( Base ` G )
  assume dchrresb.u: |- U = ( Unit ` Z )
  assume dchrresb.x: |- ( ph -> X e. D )
  assume dchrresb.Y: |- ( ph -> Y e. D )

  disjoint k ph
  disjoint U k
  disjoint X k
  disjoint Y k
  disjoint Z k
  assert |- ( ph -> ( X = Y <-> A. k e. U ( X ` k ) = ( Y ` k ) ) )

  proof
    wph
    cX
    cY
    wceq
    #
    vk
    cv
    #
    cX
    cfv
    #
    @1
    cY
    cfv
    #
    wceq
    #
    vk
    cU
    wral
    #
    @4
    vk
    cZ
    cbs
    cfv
    #
    cU
    cdif
    #
    wral
    #
    wa
    #
    @5
    wph
    @0
    @4
    vk
    @6
    wral
    #
    @9
    wph
    cX
    @6
    wfn
    #
    cY
    @6
    wfn
    #
    @0
    @10
    wb
    wph
    @6
    cc
    cX
    wf
    @11
    wph
    @6
    cD
    cG
    cN
    cX
    cZ
    dchrresb.g
    dchrresb.z
    dchrresb.b
    @6
    eqid
    #
    dchrresb.x
    dchrf
    @6
    cc
    cX
    ffn
    syl
    wph
    @6
    cc
    cY
    wf
    @12
    wph
    @6
    cD
    cG
    cN
    cY
    cZ
    dchrresb.g
    dchrresb.z
    dchrresb.b
    @13
    dchrresb.Y
    dchrf
    @6
    cc
    cY
    ffn
    syl
    vk
    @6
    cX
    cY
    eqfnfv
    syl2anc
    @10
    @4
    vk
    cU
    @7
    cun
    #
    wral
    @9
    @4
    vk
    @14
    @6
    cU
    @6
    wss
    @14
    @6
    wceq
    @6
    cZ
    cU
    @13
    dchrresb.u
    unitss
    cU
    @6
    undif
    mpbi
    raleqi
    @4
    vk
    cU
    @7
    ralunb
    bitr3i
    syl6bb
    wph
    @8
    @5
    wph
    @4
    vk
    @7
    wph
    @1
    @7
    wcel
    #
    wa
    @2
    cc0
    @3
    @15
    wph
    @1
    @6
    wcel
    #
    @1
    cU
    wcel
    #
    wn
    #
    wa
    #
    @2
    cc0
    wceq
    #
    @1
    @6
    cU
    eldif
    #
    wph
    @16
    @18
    @20
    wph
    @16
    wa
    #
    @17
    @2
    cc0
    @22
    @2
    cc0
    wne
    @17
    @22
    @1
    @6
    cD
    cU
    cG
    cN
    cX
    cZ
    dchrresb.g
    dchrresb.z
    dchrresb.b
    @13
    dchrresb.u
    wph
    cX
    cD
    wcel
    @16
    dchrresb.x
    adantr
    wph
    @16
    simpr
    #
    dchrn0
    biimpd
    necon1bd
    impr
    sylan2b
    @15
    wph
    @19
    @3
    cc0
    wceq
    #
    @21
    wph
    @16
    @18
    @24
    @22
    @17
    @3
    cc0
    @22
    @3
    cc0
    wne
    @17
    @22
    @1
    @6
    cD
    cU
    cG
    cN
    cY
    cZ
    dchrresb.g
    dchrresb.z
    dchrresb.b
    @13
    dchrresb.u
    wph
    cY
    cD
    wcel
    @16
    dchrresb.Y
    adantr
    @23
    dchrn0
    biimpd
    necon1bd
    impr
    sylan2b
    eqtr4d
    ralrimiva
    biantrud
    bitr4d
end
