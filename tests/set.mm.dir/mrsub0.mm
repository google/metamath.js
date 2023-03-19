include "crn.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cmrex.mm"
include "cmvar.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "c0.mm"
include "n0i.mm"
include "wn.mm"
include "cmrsub.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "rneqd.mm"
include "rn0.mm"
include "syl6eq.mm"
include "nsyl2.mm"
include "wfun.mm"
include "cima.mm"
include "cpm.mm"
include "wf.mm"
include "eqid.mm"
include "mrsubff.mm"
include "ffun.mm"
include "3syl.mm"
include "mrsubrn.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "fvelima.mm"
include "syl2anc.mm"
include "wa.mm"
include "cmcn.mm"
include "cun.mm"
include "cfrmd.mm"
include "cs1.mm"
include "cif.mm"
include "cmpt.mm"
include "ccom.mm"
include "cgsu.mm"
include "wss.mm"
include "elmapi.mm"
include "adantl.mm"
include "ssid.mm"
include "a1i.mm"
include "cword.mm"
include "wrd0.mm"
include "mrexval.mm"
include "adantr.mm"
include "syl5eleqr.mm"
include "mrsubval.mm"
include "syl3anc.mm"
include "co02.mm"
include "oveq2i.mm"
include "frmd0.mm"
include "gsum0.mm"
include "eqtri.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "sylc.mm"

theorem mrsub0
  let cS: class S
  let cT: class T
  let cF: class F
  let vc: setvar c
  let vf: setvar f
  let vr: setvar r
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cR: class R
  let vw: setvar w
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume mrsubccat.s: |- S = ( mRSubst ` T )


  assert |- ( F e. ran S -> ( F ` (/) ) = (/) )

  proof
    cF
    cS
    crn
    #
    wcel
    #
    cT
    cvv
    wcel
    #
    vf
    cv
    #
    cS
    cfv
    #
    cF
    wceq
    #
    vf
    cT
    cmrex
    cfv
    #
    cT
    cmvar
    cfv
    #
    cmap
    co
    #
    wrex
    #
    c0
    cF
    cfv
    #
    c0
    wceq
    #
    @1
    @0
    c0
    wceq
    @2
    @0
    cF
    n0i
    @2
    wn
    #
    @0
    c0
    crn
    c0
    @12
    cS
    c0
    @12
    cS
    cT
    cmrsub
    cfv
    c0
    mrsubccat.s
    cT
    cmrsub
    fvprc
    syl5eq
    rneqd
    rn0
    syl6eq
    nsyl2
    #
    @1
    cS
    wfun
    #
    cF
    cS
    @8
    cima
    #
    wcel
    #
    @9
    @1
    @2
    @6
    @7
    cpm
    co
    #
    @6
    @6
    cmap
    co
    #
    cS
    wf
    @14
    @13
    @6
    cS
    cT
    @7
    cvv
    @7
    eqid
    #
    @6
    eqid
    #
    mrsubccat.s
    mrsubff
    @17
    @18
    cS
    ffun
    3syl
    @1
    @16
    @0
    @15
    cF
    @6
    cS
    cT
    @7
    @19
    @20
    mrsubccat.s
    mrsubrn
    eleq2i
    biimpi
    vf
    cF
    @8
    cS
    fvelima
    syl2anc
    @2
    @5
    @11
    vf
    @8
    @2
    @3
    @8
    wcel
    #
    wa
    #
    c0
    @4
    cfv
    #
    c0
    wceq
    @5
    @11
    @22
    @23
    cT
    cmcn
    cfv
    #
    @7
    cun
    #
    cfrmd
    cfv
    #
    vv
    @25
    vv
    cv
    #
    @7
    wcel
    @27
    @3
    cfv
    @27
    cs1
    cif
    cmpt
    #
    c0
    ccom
    #
    cgsu
    co
    #
    c0
    @22
    @7
    @6
    @3
    wf
    #
    @7
    @7
    wss
    #
    c0
    @6
    wcel
    @23
    @30
    wceq
    @21
    @31
    @2
    @3
    @6
    @7
    elmapi
    adantl
    @32
    @22
    @7
    ssid
    a1i
    @22
    c0
    @25
    cword
    #
    @6
    @25
    wrd0
    @2
    @6
    @33
    wceq
    @21
    @24
    @6
    cT
    @7
    cvv
    @24
    eqid
    #
    @19
    @20
    mrexval
    adantr
    syl5eleqr
    vv
    @7
    @24
    @6
    cS
    cT
    @3
    @26
    @7
    c0
    @34
    @19
    @20
    mrsubccat.s
    @26
    eqid
    #
    mrsubval
    syl3anc
    @30
    @26
    c0
    cgsu
    co
    c0
    @29
    c0
    @26
    cgsu
    @28
    co02
    oveq2i
    @26
    c0
    @25
    @26
    @35
    frmd0
    gsum0
    eqtri
    syl6eq
    @5
    @23
    @10
    c0
    c0
    @4
    cF
    fveq1
    eqeq1d
    syl5ibcom
    rexlimdva
    sylc
end
