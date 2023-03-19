include "cdiv.mm"
include "cof.mm"
include "co.mm"
include "cdv.mm"
include "cmul.mm"
include "cmin.mm"
include "cc.mm"
include "ccncf.mm"
include "wcel.mm"
include "wf.mm"
include "cdm.mm"
include "wceq.mm"
include "cncff.mm"
include "fdm.mm"
include "3syl.mm"
include "dvdivf.mm"
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
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "difssd.mm"
include "fssd.mm"
include "dvbsss.mm"
include "syl6eqssr.mm"
include "dvcn.mm"
include "syl31anc.mm"
include "mulcncff.mm"
include "subcncff.mm"
include "cvv.mm"
include "cv.mm"
include "wne.mm"
include "eldifi.mm"
include "adantr.mm"
include "adantl.mm"
include "mulcld.mm"
include "eldifsni.mm"
include "mulne0d.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "ssexd.mm"
include "inidm.mm"
include "off.mm"
include "wb.mm"
include "cncffvrn.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "divcncff.mm"
include "eqeltrd.mm"

theorem dvdivcncf
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume dvdivcncf.s: |- ( ph -> S e. { RR , CC } )
  assume dvdivcncf.f: |- ( ph -> F : X --> CC )
  assume dvdivcncf.g: |- ( ph -> G : X --> ( CC \ { 0 } ) )
  assume dvdivcncf.fdv: |- ( ph -> ( S _D F ) e. ( X -cn-> CC ) )
  assume dvdivcncf.gdv: |- ( ph -> ( S _D G ) e. ( X -cn-> CC ) )


  assert |- ( ph -> ( S _D ( F oF / G ) ) e. ( X -cn-> CC ) )

  proof
    wph
    cS
    cF
    cG
    cdiv
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
    cmul
    cof
    #
    co
    #
    cS
    cG
    cdv
    co
    #
    cF
    @2
    co
    #
    cmin
    cof
    co
    #
    cG
    cG
    @2
    co
    #
    @0
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
    dvdivcncf.s
    dvdivcncf.f
    dvdivcncf.g
    wph
    @1
    @8
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
    dvdivcncf.fdv
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
    @4
    @8
    wcel
    cX
    cc
    @4
    wf
    @4
    cdm
    cX
    wceq
    #
    dvdivcncf.gdv
    cX
    cc
    @4
    cncff
    cX
    cc
    @4
    fdm
    3syl
    #
    dvdivf
    wph
    @6
    @7
    cX
    wph
    @3
    @5
    cX
    wph
    @1
    cG
    cX
    dvdivcncf.fdv
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
    @12
    cG
    @8
    wcel
    cS
    cr
    wceq
    #
    @14
    wi
    #
    cS
    cc
    wceq
    #
    @14
    wi
    #
    wa
    wph
    @16
    @18
    wo
    #
    @14
    @17
    @19
    @16
    @14
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
    #
    wcel
    @20
    dvdivcncf.s
    cS
    cr
    cc
    elpri
    syl
    @14
    @16
    @18
    pm3.44
    mpsyl
    #
    wph
    cX
    cc
    cc0
    csn
    #
    cdif
    #
    cc
    cG
    dvdivcncf.g
    wph
    cc
    @23
    difssd
    #
    fssd
    wph
    cX
    @9
    cS
    @11
    cS
    cF
    dvbsss
    syl6eqssr
    #
    @13
    cX
    cS
    cG
    dvcn
    syl31anc
    #
    mulcncff
    wph
    @4
    cF
    cX
    dvdivcncf.gdv
    wph
    @14
    cX
    cc
    cF
    wf
    @15
    @10
    cF
    @8
    wcel
    @22
    dvdivcncf.f
    @26
    @11
    cX
    cS
    cF
    dvcn
    syl31anc
    mulcncff
    subcncff
    wph
    @7
    cX
    @24
    ccncf
    co
    wcel
    #
    cX
    @24
    @7
    wf
    #
    wph
    vx
    vy
    cX
    cX
    cX
    cmul
    @24
    @24
    @24
    cG
    cG
    cvv
    cvv
    vx
    cv
    #
    @24
    wcel
    #
    vy
    cv
    #
    @24
    wcel
    #
    wa
    #
    @30
    @32
    cmul
    co
    #
    @24
    wcel
    #
    wph
    @34
    @35
    cc
    wcel
    @35
    cc0
    wne
    @36
    @34
    @30
    @32
    @31
    @30
    cc
    wcel
    @33
    @30
    cc
    @23
    eldifi
    adantr
    #
    @33
    @32
    cc
    wcel
    @31
    @32
    cc
    @23
    eldifi
    adantl
    #
    mulcld
    @34
    @30
    @32
    @37
    @38
    @31
    @30
    cc0
    wne
    @33
    @30
    cc
    cc0
    eldifsni
    adantr
    @33
    @32
    cc0
    wne
    @31
    @32
    cc
    cc0
    eldifsni
    adantl
    mulne0d
    @35
    cc
    cc0
    eldifsn
    sylanbrc
    adantl
    dvdivcncf.g
    dvdivcncf.g
    wph
    cX
    cS
    @21
    dvdivcncf.s
    @26
    ssexd
    #
    @39
    cX
    inidm
    off
    wph
    @24
    cc
    wss
    @7
    @8
    wcel
    @28
    @29
    wb
    @25
    wph
    cG
    cG
    cX
    @27
    @27
    mulcncff
    cX
    cc
    @24
    @7
    cncffvrn
    syl2anc
    mpbird
    divcncff
    eqeltrd
end
