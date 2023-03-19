include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cpr.mm"
include "csca.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cprds.mm"
include "co.mm"
include "cbs.mm"
include "wss.mm"
include "cple.mm"
include "wbr.mm"
include "wral.mm"
include "copab.mm"
include "cofr.mm"
include "cin.mm"
include "vex.mm"
include "prss.mm"
include "eqid.mm"
include "pwsval.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "sseq2d.mm"
include "syl5bb.mm"
include "anbi1d.mm"
include "wceq.mm"
include "simpll.mm"
include "fvconst2g.mm"
include "sylan.mm"
include "syl6eqr.mm"
include "breqd.mm"
include "ralbidva.mm"
include "wf.mm"
include "wfn.mm"
include "simplr.mm"
include "simprl.mm"
include "pwselbas.mm"
include "ffn.mm"
include "syl.mm"
include "simprr.mm"
include "inidm.mm"
include "eqidd.mm"
include "ofrfval.mm"
include "bitr4d.mm"
include "pm5.32da.mm"
include "w3a.mm"
include "brinxp2.mm"
include "df-3an.mm"
include "bitri.mm"
include "syl6bbr.mm"
include "bitr3d.mm"
include "opabbidv.mm"
include "cvv.mm"
include "fvexd.mm"
include "simpr.mm"
include "snex.mm"
include "xpexg.mm"
include "sylancl.mm"
include "c0.mm"
include "wne.mm"
include "cdm.mm"
include "snnzg.mm"
include "adantr.mm"
include "dmxp.mm"
include "prdsle.mm"
include "eqtrd.mm"
include "wrel.mm"
include "inss2.mm"
include "relxp.mm"
include "relss.mm"
include "mp2.mm"
include "a1i.mm"
include "dfrel4v.mm"
include "sylib.mm"
include "3eqtr4d.mm"

theorem pwsle
  let cB: class B
  let cR: class R
  let cI: class I
  let c.le: class .<_
  let cO: class O
  let cV: class V
  let cW: class W
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let cF: class F
  let cG: class G
  let wph: wff ph
  assume pwsle.y: |- Y = ( R ^s I )
  assume pwsle.v: |- B = ( Base ` Y )
  assume pwsle.o: |- O = ( le ` R )
  assume pwsle.l: |- .<_ = ( le ` Y )


  assert |- ( ( R e. V /\ I e. W ) -> .<_ = ( oR O i^i ( B X. B ) ) )

  proof
    cR
    cV
    wcel
    #
    cI
    cW
    wcel
    #
    wa
    #
    vf
    cv
    #
    vg
    cv
    #
    cpr
    #
    cR
    csca
    cfv
    #
    cI
    cR
    csn
    #
    cxp
    #
    cprds
    co
    #
    cbs
    cfv
    #
    wss
    #
    vx
    cv
    #
    @3
    cfv
    #
    @12
    @4
    cfv
    #
    @12
    @8
    cfv
    #
    cple
    cfv
    #
    wbr
    #
    vx
    cI
    wral
    #
    wa
    #
    vf
    vg
    copab
    #
    @3
    @4
    cO
    cofr
    #
    cB
    cB
    cxp
    #
    cin
    #
    wbr
    #
    vf
    vg
    copab
    #
    c.le
    @23
    @2
    @19
    @24
    vf
    vg
    @2
    @3
    cB
    wcel
    #
    @4
    cB
    wcel
    #
    wa
    #
    @18
    wa
    #
    @19
    @24
    @2
    @28
    @11
    @18
    @28
    @5
    cB
    wss
    @2
    @11
    @3
    @4
    cB
    vf
    vex
    vg
    vex
    prss
    @2
    cB
    @10
    @5
    @2
    cB
    cY
    cbs
    cfv
    @10
    pwsle.v
    @2
    cY
    @9
    cbs
    cR
    @6
    cI
    cV
    cW
    cY
    pwsle.y
    @6
    eqid
    pwsval
    #
    fveq2d
    syl5eq
    sseq2d
    syl5bb
    anbi1d
    @2
    @29
    @28
    @3
    @4
    @21
    wbr
    #
    wa
    #
    @24
    @2
    @28
    @18
    @31
    @2
    @28
    wa
    #
    @18
    @13
    @14
    cO
    wbr
    #
    vx
    cI
    wral
    @31
    @33
    @17
    @34
    vx
    cI
    @33
    @12
    cI
    wcel
    #
    wa
    #
    @16
    cO
    @13
    @14
    @36
    @16
    cR
    cple
    cfv
    cO
    @36
    @15
    cR
    cple
    @33
    @0
    @35
    @15
    cR
    wceq
    @0
    @1
    @28
    simpll
    #
    cI
    cR
    @12
    cV
    fvconst2g
    sylan
    fveq2d
    pwsle.o
    syl6eqr
    breqd
    ralbidva
    @33
    vx
    cI
    cI
    @13
    @14
    cO
    cI
    @3
    @4
    cW
    cW
    @33
    cI
    cR
    cbs
    cfv
    #
    @3
    wf
    @3
    cI
    wfn
    @33
    @38
    cR
    cI
    cB
    cV
    @3
    cY
    cW
    pwsle.y
    @38
    eqid
    #
    pwsle.v
    @37
    @0
    @1
    @28
    simplr
    #
    @2
    @26
    @27
    simprl
    pwselbas
    cI
    @38
    @3
    ffn
    syl
    @33
    cI
    @38
    @4
    wf
    @4
    cI
    wfn
    @33
    @38
    cR
    cI
    cB
    cV
    @4
    cY
    cW
    pwsle.y
    @39
    pwsle.v
    @37
    @40
    @2
    @26
    @27
    simprr
    pwselbas
    cI
    @38
    @4
    ffn
    syl
    @40
    @40
    cI
    inidm
    @36
    @13
    eqidd
    @36
    @14
    eqidd
    ofrfval
    bitr4d
    pm5.32da
    @24
    @26
    @27
    @31
    w3a
    @32
    @3
    @4
    cB
    cB
    @21
    brinxp2
    @26
    @27
    @31
    df-3an
    bitri
    syl6bbr
    bitr3d
    opabbidv
    @2
    c.le
    @9
    cple
    cfv
    #
    @20
    @2
    c.le
    cY
    cple
    cfv
    @41
    pwsle.l
    @2
    cY
    @9
    cple
    @30
    fveq2d
    syl5eq
    @2
    vx
    @10
    @9
    @8
    @6
    vf
    vg
    cI
    @41
    cvv
    cvv
    @9
    eqid
    @2
    cR
    csca
    fvexd
    @2
    @1
    @7
    cvv
    wcel
    @8
    cvv
    wcel
    @0
    @1
    simpr
    cR
    snex
    cI
    @7
    cW
    cvv
    xpexg
    sylancl
    @10
    eqid
    @2
    @7
    c0
    wne
    #
    @8
    cdm
    cI
    wceq
    @0
    @42
    @1
    cR
    cV
    snnzg
    adantr
    cI
    @7
    dmxp
    syl
    @41
    eqid
    prdsle
    eqtrd
    @2
    @23
    wrel
    #
    @23
    @25
    wceq
    @43
    @2
    @23
    @22
    wss
    @22
    wrel
    @43
    @21
    @22
    inss2
    cB
    cB
    relxp
    @23
    @22
    relss
    mp2
    a1i
    vf
    vg
    @23
    dfrel4v
    sylib
    3eqtr4d
end
