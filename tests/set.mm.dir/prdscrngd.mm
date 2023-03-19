include "crg.mm"
include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "ccmn.mm"
include "ccrg.mm"
include "wf.mm"
include "wss.mm"
include "cv.mm"
include "crngring.mm"
include "ssriv.mm"
include "fss.mm"
include "sylancl.mm"
include "prdsringd.mm"
include "ccom.mm"
include "cprds.mm"
include "co.mm"
include "eqid.mm"
include "cres.mm"
include "wfn.mm"
include "wral.mm"
include "cvv.mm"
include "fnmgp.mm"
include "ssv.mm"
include "fnssres.mm"
include "mp2an.mm"
include "fvres.mm"
include "crngmgp.mm"
include "eqeltrd.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"
include "fco2.mm"
include "sylancr.mm"
include "prdscmnd.mm"
include "cbs.mm"
include "eqidd.mm"
include "wceq.mm"
include "cplusg.mm"
include "ffn.mm"
include "syl.mm"
include "prdsmgp.mm"
include "simpld.mm"
include "wa.mm"
include "simprd.mm"
include "oveqdr.mm"
include "cmnpropd.mm"
include "mpbird.mm"
include "iscrng.mm"
include "sylanbrc.mm"

theorem prdscrngd
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume prdscrngd.y: |- Y = ( S Xs_ R )
  assume prdscrngd.i: |- ( ph -> I e. W )
  assume prdscrngd.s: |- ( ph -> S e. V )
  assume prdscrngd.r: |- ( ph -> R : I --> CRing )


  assert |- ( ph -> Y e. CRing )

  proof
    wph
    cY
    crg
    wcel
    cY
    cmgp
    cfv
    #
    ccmn
    wcel
    #
    cY
    ccrg
    wcel
    wph
    cR
    cS
    cI
    cV
    cW
    cY
    prdscrngd.y
    prdscrngd.i
    prdscrngd.s
    wph
    cI
    ccrg
    cR
    wf
    #
    ccrg
    crg
    wss
    cI
    crg
    cR
    wf
    prdscrngd.r
    vx
    ccrg
    crg
    vx
    cv
    #
    crngring
    ssriv
    cI
    ccrg
    crg
    cR
    fss
    sylancl
    prdsringd
    wph
    @1
    cS
    cmgp
    cR
    ccom
    #
    cprds
    co
    #
    ccmn
    wcel
    wph
    @4
    cS
    cI
    cV
    cW
    @5
    @5
    eqid
    #
    prdscrngd.i
    prdscrngd.s
    wph
    ccrg
    ccmn
    cmgp
    ccrg
    cres
    #
    wf
    #
    @2
    cI
    ccmn
    @4
    wf
    @8
    @7
    ccrg
    wfn
    #
    @3
    @7
    cfv
    #
    ccmn
    wcel
    #
    vx
    ccrg
    wral
    cmgp
    cvv
    wfn
    ccrg
    cvv
    wss
    @9
    fnmgp
    ccrg
    ssv
    cvv
    ccrg
    cmgp
    fnssres
    mp2an
    @11
    vx
    ccrg
    @3
    ccrg
    wcel
    @10
    @3
    cmgp
    cfv
    #
    ccmn
    @3
    ccrg
    cmgp
    fvres
    @3
    @12
    @12
    eqid
    crngmgp
    eqeltrd
    rgen
    vx
    ccrg
    ccmn
    @7
    ffnfv
    mpbir2an
    prdscrngd.r
    cI
    ccrg
    ccmn
    cmgp
    cR
    fco2
    sylancr
    prdscmnd
    wph
    vx
    vy
    @0
    cbs
    cfv
    #
    @0
    @5
    wph
    @13
    eqidd
    wph
    @13
    @5
    cbs
    cfv
    wceq
    #
    @0
    cplusg
    cfv
    #
    @5
    cplusg
    cfv
    #
    wceq
    #
    wph
    cR
    cS
    cI
    @0
    cW
    cV
    cY
    @5
    prdscrngd.y
    @0
    eqid
    #
    @6
    prdscrngd.i
    prdscrngd.s
    wph
    @2
    cR
    cI
    wfn
    prdscrngd.r
    cI
    ccrg
    cR
    ffn
    syl
    prdsmgp
    #
    simpld
    wph
    @3
    @13
    wcel
    vy
    cv
    @13
    wcel
    wa
    vx
    vy
    @15
    @16
    wph
    @14
    @17
    @19
    simprd
    oveqdr
    cmnpropd
    mpbird
    cY
    @0
    @18
    iscrng
    sylanbrc
end
