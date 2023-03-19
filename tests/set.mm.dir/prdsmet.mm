include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "cr.mm"
include "wf.mm"
include "cme.mm"
include "cfn.mm"
include "cv.mm"
include "wa.mm"
include "metxmet.mm"
include "syl.mm"
include "prdsxmet.mm"
include "wfn.mm"
include "co.mm"
include "wral.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "prdsdsf.mm"
include "ffn.mm"
include "cmpt.mm"
include "crn.mm"
include "csn.mm"
include "cun.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "adantr.mm"
include "ralrimiva.mm"
include "simprl.mm"
include "simprr.mm"
include "prdsdsval3.mm"
include "wss.mm"
include "prdsbascl.mm"
include "r19.26.mm"
include "wi.mm"
include "metcl.mm"
include "3expib.mm"
include "ralimdva.mm"
include "syl5bir.mm"
include "mp2and.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylib.mm"
include "frn.mm"
include "0red.mm"
include "snssd.mm"
include "unssd.mm"
include "wor.mm"
include "c0.mm"
include "wne.mm"
include "xrltso.mm"
include "a1i.mm"
include "mptfi.mm"
include "rnfi.mm"
include "3syl.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "ssun2.mm"
include "c0ex.mm"
include "snss.mm"
include "mpbir.mm"
include "ne0i.mm"
include "mp1i.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "fisupcl.mm"
include "syl13anc.mm"
include "sseldd.mm"
include "eqeltrd.mm"
include "ralrimivva.mm"
include "ffnov.mm"
include "sylanbrc.mm"
include "ismet2.mm"

theorem prdsmet
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let cE: class E
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  let vg: setvar g
  assume prdsmet.y: |- Y = ( S Xs_ ( x e. I |-> R ) )
  assume prdsmet.b: |- B = ( Base ` Y )
  assume prdsmet.v: |- V = ( Base ` R )
  assume prdsmet.e: |- E = ( ( dist ` R ) |` ( V X. V ) )
  assume prdsmet.d: |- D = ( dist ` Y )
  assume prdsmet.s: |- ( ph -> S e. W )
  assume prdsmet.i: |- ( ph -> I e. Fin )
  assume prdsmet.r: |- ( ( ph /\ x e. I ) -> R e. Z )
  assume prdsmet.m: |- ( ( ph /\ x e. I ) -> E e. ( Met ` V ) )

  disjoint I x
  disjoint ph x
  disjoint f g
  disjoint B f
  disjoint B g
  disjoint D f
  disjoint D g
  disjoint f x
  disjoint f ph
  disjoint g x
  disjoint g ph
  assert |- ( ph -> D e. ( Met ` B ) )

  proof
    wph
    cD
    cB
    cxmt
    cfv
    wcel
    cB
    cB
    cxp
    #
    cr
    cD
    wf
    #
    cD
    cB
    cme
    cfv
    wcel
    wph
    vx
    cB
    cD
    cR
    cS
    cE
    cI
    cV
    cW
    cfn
    cY
    cZ
    prdsmet.y
    prdsmet.b
    prdsmet.v
    prdsmet.e
    prdsmet.d
    prdsmet.s
    prdsmet.i
    prdsmet.r
    wph
    vx
    cv
    #
    cI
    wcel
    wa
    #
    cE
    cV
    cme
    cfv
    wcel
    #
    cE
    cV
    cxmt
    cfv
    wcel
    prdsmet.m
    cE
    cV
    metxmet
    syl
    #
    prdsxmet
    wph
    cD
    @0
    wfn
    #
    vf
    cv
    #
    vg
    cv
    #
    cD
    co
    #
    cr
    wcel
    #
    vg
    cB
    wral
    vf
    cB
    wral
    @1
    wph
    @0
    cc0
    cpnf
    cicc
    co
    #
    cD
    wf
    @6
    wph
    vx
    cB
    cD
    cR
    cS
    cE
    cI
    cV
    cW
    cfn
    cY
    cZ
    prdsmet.y
    prdsmet.b
    prdsmet.v
    prdsmet.e
    prdsmet.d
    prdsmet.s
    prdsmet.i
    prdsmet.r
    @5
    prdsdsf
    @0
    @11
    cD
    ffn
    syl
    wph
    @10
    vf
    vg
    cB
    cB
    wph
    @7
    cB
    wcel
    #
    @8
    cB
    wcel
    #
    wa
    #
    wa
    #
    @9
    vx
    cI
    @2
    @7
    cfv
    #
    @2
    @8
    cfv
    #
    cE
    co
    #
    cmpt
    #
    crn
    #
    cc0
    csn
    #
    cun
    #
    cxr
    clt
    csup
    #
    cr
    @15
    vx
    cB
    cD
    cR
    cS
    cE
    @7
    @8
    cI
    cV
    cW
    cfn
    cZ
    cY
    prdsmet.y
    prdsmet.b
    wph
    cS
    cW
    wcel
    @14
    prdsmet.s
    adantr
    #
    wph
    cI
    cfn
    wcel
    #
    @14
    prdsmet.i
    adantr
    #
    wph
    cR
    cZ
    wcel
    #
    vx
    cI
    wral
    @14
    wph
    @27
    vx
    cI
    prdsmet.r
    ralrimiva
    adantr
    #
    wph
    @12
    @13
    simprl
    #
    wph
    @12
    @13
    simprr
    #
    prdsmet.v
    prdsmet.e
    prdsmet.d
    prdsdsval3
    @15
    @22
    cr
    @23
    @15
    @20
    @21
    cr
    @15
    cI
    cr
    @19
    wf
    #
    @20
    cr
    wss
    @15
    @18
    cr
    wcel
    #
    vx
    cI
    wral
    #
    @31
    @15
    @16
    cV
    wcel
    #
    vx
    cI
    wral
    #
    @17
    cV
    wcel
    #
    vx
    cI
    wral
    #
    @33
    @15
    vx
    cB
    cR
    cS
    @7
    cI
    cV
    cW
    cfn
    cZ
    cY
    prdsmet.y
    prdsmet.b
    @24
    @26
    @28
    prdsmet.v
    @29
    prdsbascl
    @15
    vx
    cB
    cR
    cS
    @8
    cI
    cV
    cW
    cfn
    cZ
    cY
    prdsmet.y
    prdsmet.b
    @24
    @26
    @28
    prdsmet.v
    @30
    prdsbascl
    @35
    @37
    wa
    @34
    @36
    wa
    #
    vx
    cI
    wral
    #
    @15
    @33
    @34
    @36
    vx
    cI
    r19.26
    wph
    @39
    @33
    wi
    @14
    wph
    @38
    @32
    vx
    cI
    @3
    @4
    @38
    @32
    wi
    prdsmet.m
    @4
    @34
    @36
    @32
    @16
    @17
    cE
    cV
    metcl
    3expib
    syl
    ralimdva
    adantr
    syl5bir
    mp2and
    vx
    cI
    cr
    @18
    @19
    @19
    eqid
    fmpt
    sylib
    cI
    cr
    @19
    frn
    syl
    @15
    cc0
    cr
    @15
    0red
    snssd
    unssd
    #
    @15
    cxr
    clt
    wor
    #
    @22
    cfn
    wcel
    #
    @22
    c0
    wne
    #
    @22
    cxr
    wss
    @23
    @22
    wcel
    @41
    @15
    xrltso
    a1i
    @15
    @20
    cfn
    wcel
    #
    @21
    cfn
    wcel
    @42
    @15
    @25
    @19
    cfn
    wcel
    @44
    @26
    vx
    cI
    @18
    mptfi
    @19
    rnfi
    3syl
    cc0
    snfi
    @20
    @21
    unfi
    sylancl
    cc0
    @22
    wcel
    #
    @43
    @15
    @45
    @21
    @22
    wss
    @21
    @20
    ssun2
    cc0
    @22
    c0ex
    snss
    mpbir
    @22
    cc0
    ne0i
    mp1i
    @15
    @22
    cr
    cxr
    @40
    ressxr
    syl6ss
    cxr
    @22
    clt
    fisupcl
    syl13anc
    sseldd
    eqeltrd
    ralrimivva
    vf
    vg
    cB
    cB
    cr
    cD
    ffnov
    sylanbrc
    cD
    cB
    ismet2
    sylanbrc
end
