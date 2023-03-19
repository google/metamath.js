include "cupgr.mm"
include "wcel.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cuspgr.mm"
include "cpr.mm"
include "cs1.mm"
include "cop.mm"
include "opeq2i.mm"
include "eqtri.mm"
include "cvv.mm"
include "uspgr2v1e2w.mm"
include "mp2an.mm"
include "eqeltri.mm"
include "uspgrupgr.mm"
include "ax-mp.mm"
include "cdm.mm"
include "cword.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "wlk2v2elem1.mm"
include "c3.mm"
include "cs3.mm"
include "prid1.mm"
include "prid2.mm"
include "s3cl.mm"
include "mp3an.mm"
include "wrdf.mm"
include "fveq2i.mm"
include "s3len.mm"
include "eqtr2i.mm"
include "oveq2i.mm"
include "feq2i.mm"
include "mpbir.mm"
include "c2.mm"
include "cs2.mm"
include "s2len.mm"
include "cmin.mm"
include "cz.mm"
include "3z.mm"
include "fzoval.mm"
include "3m1e2.mm"
include "wlk2v2elem2.mm"
include "3pm3.2i.mm"
include "cvtx.mm"
include "prex.mm"
include "s1cli.mm"
include "opvtxfv.mm"
include "ciedg.mm"
include "opiedgfv.mm"
include "upgriswlk.mm"
include "mpbiri.mm"

theorem wlk2v2e
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  let cX: class X
  let cY: class Y
  let vk: setvar k
  assume wlk2v2e.i: |- I = <" { X , Y } ">
  assume wlk2v2e.f: |- F = <" 0 0 ">
  assume wlk2v2e.x: |- X e. _V
  assume wlk2v2e.y: |- Y e. _V
  assume wlk2v2e.p: |- P = <" X Y X ">
  assume wlk2v2e.g: |- G = <. { X , Y } , I >.


  assert |- F ( Walks ` G ) P

  proof
    cG
    cupgr
    wcel
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cG
    cuspgr
    wcel
    @0
    cG
    cX
    cY
    cpr
    #
    @2
    cs1
    #
    cop
    #
    cuspgr
    cG
    @2
    cI
    cop
    #
    @4
    wlk2v2e.g
    cI
    @3
    @2
    wlk2v2e.i
    opeq2i
    eqtri
    cX
    cvv
    wcel
    cY
    cvv
    wcel
    @4
    cuspgr
    wcel
    wlk2v2e.x
    wlk2v2e.y
    cX
    cY
    cvv
    cvv
    uspgr2v1e2w
    mp2an
    eqeltri
    cG
    uspgrupgr
    ax-mp
    @0
    @1
    cF
    cI
    cdm
    cword
    wcel
    #
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    #
    @2
    cP
    wf
    #
    vk
    cv
    #
    cF
    cfv
    cI
    cfv
    @10
    cP
    cfv
    @10
    c1
    caddc
    co
    cP
    cfv
    cpr
    wceq
    vk
    cc0
    @7
    cfzo
    co
    wral
    #
    w3a
    @6
    @9
    @11
    cF
    cI
    cX
    cY
    wlk2v2e.i
    wlk2v2e.f
    wlk2v2elem1
    @9
    cc0
    c3
    cfzo
    co
    #
    @2
    cP
    wf
    #
    @13
    cc0
    cP
    chash
    cfv
    #
    cfzo
    co
    #
    @2
    cP
    wf
    #
    cP
    @2
    cword
    #
    wcel
    @16
    cP
    cX
    cY
    cX
    cs3
    #
    @17
    wlk2v2e.p
    cX
    @2
    wcel
    #
    cY
    @2
    wcel
    @19
    @18
    @17
    wcel
    cX
    cY
    wlk2v2e.x
    prid1
    #
    cX
    cY
    wlk2v2e.y
    prid2
    @20
    cX
    cY
    cX
    @2
    s3cl
    mp3an
    eqeltri
    @2
    cP
    wrdf
    ax-mp
    @12
    @15
    @2
    cP
    c3
    @14
    cc0
    cfzo
    @14
    @18
    chash
    cfv
    c3
    cP
    @18
    chash
    wlk2v2e.p
    fveq2i
    cX
    cY
    cX
    s3len
    eqtr2i
    oveq2i
    feq2i
    mpbir
    @8
    @12
    @2
    cP
    @8
    cc0
    c2
    cfz
    co
    #
    @12
    @7
    c2
    cc0
    cfz
    @7
    cc0
    cc0
    cs2
    #
    chash
    cfv
    c2
    cF
    @22
    chash
    wlk2v2e.f
    fveq2i
    cc0
    cc0
    s2len
    eqtri
    oveq2i
    @12
    cc0
    c3
    c1
    cmin
    co
    #
    cfz
    co
    #
    @21
    c3
    cz
    wcel
    @12
    @24
    wceq
    3z
    cc0
    c3
    fzoval
    ax-mp
    @23
    c2
    cc0
    cfz
    3m1e2
    oveq2i
    eqtr2i
    eqtri
    feq2i
    mpbir
    cP
    vk
    cF
    cI
    cX
    cY
    wlk2v2e.i
    wlk2v2e.f
    wlk2v2e.x
    wlk2v2e.y
    wlk2v2e.p
    wlk2v2elem2
    3pm3.2i
    cP
    vk
    cF
    cG
    cI
    @2
    cG
    cvtx
    cfv
    @5
    cvtx
    cfv
    #
    @2
    cG
    @5
    cvtx
    wlk2v2e.g
    fveq2i
    @2
    cvv
    wcel
    #
    cI
    cvv
    cword
    #
    wcel
    #
    @25
    @2
    wceq
    cX
    cY
    prex
    #
    cI
    @3
    @27
    wlk2v2e.i
    @2
    s1cli
    eqeltri
    #
    cI
    @2
    cvv
    @27
    opvtxfv
    mp2an
    eqtr2i
    cG
    ciedg
    cfv
    @5
    ciedg
    cfv
    #
    cI
    cG
    @5
    ciedg
    wlk2v2e.g
    fveq2i
    @26
    @28
    @31
    cI
    wceq
    @29
    @30
    cI
    @2
    cvv
    @27
    opiedgfv
    mp2an
    eqtr2i
    upgriswlk
    mpbiri
    ax-mp
end
