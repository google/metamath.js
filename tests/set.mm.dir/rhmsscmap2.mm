include "crh.mm"
include "cxp.mm"
include "cres.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "cmap.mm"
include "co.mm"
include "cmpt2.mm"
include "cssc.mm"
include "wbr.mm"
include "wss.mm"
include "wral.mm"
include "ssid.mm"
include "a1i.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "eqid.mm"
include "rhmf.mm"
include "simpr.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "pm3.2i.mm"
include "elmapg.mm"
include "mp1i.mm"
include "mpbird.mm"
include "ex.mm"
include "syl5.mm"
include "ssrdv.mm"
include "wceq.mm"
include "ovres.mm"
include "adantl.mm"
include "eqidd.mm"
include "weq.mm"
include "fveq2.mm"
include "oveqan12rd.mm"
include "simpl.mm"
include "ovexd.mm"
include "ovmpt2d.mm"
include "3sstr4d.mm"
include "ralrimivva.mm"
include "crg.mm"
include "wfn.mm"
include "rhmfn.mm"
include "cin.mm"
include "inss1.mm"
include "syl6eqss.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "fnssres.mm"
include "ovex.mm"
include "fnmpt2i.mm"
include "incom.mm"
include "inex1g.mm"
include "syl.mm"
include "syl5eqel.mm"
include "eqeltrd.mm"
include "isssc.mm"
include "mpbir2and.mm"

theorem rhmsscmap2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cU: class U
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vh: setvar h
  let vk: setvar k
  assume rhmsscmap.u: |- ( ph -> U e. V )
  assume rhmsscmap.r: |- ( ph -> R = ( Ring i^i U ) )

  disjoint R x
  disjoint R y
  disjoint x y
  disjoint R a
  disjoint R b
  disjoint R h
  disjoint a b
  disjoint a h
  disjoint b h
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint a ph
  disjoint b ph
  disjoint h ph
  disjoint k x
  assert |- ( ph -> ( RingHom |` ( R X. R ) ) C_cat ( x e. R , y e. R |-> ( ( Base ` y ) ^m ( Base ` x ) ) ) )

  proof
    wph
    crh
    cR
    cR
    cxp
    #
    cres
    #
    vx
    vy
    cR
    cR
    vy
    cv
    #
    cbs
    cfv
    #
    vx
    cv
    #
    cbs
    cfv
    #
    cmap
    co
    #
    cmpt2
    #
    cssc
    wbr
    cR
    cR
    wss
    #
    va
    cv
    #
    vb
    cv
    #
    @1
    co
    #
    @9
    @10
    @7
    co
    #
    wss
    #
    vb
    cR
    wral
    va
    cR
    wral
    @8
    wph
    cR
    ssid
    a1i
    wph
    @13
    va
    vb
    cR
    cR
    wph
    @9
    cR
    wcel
    #
    @10
    cR
    wcel
    #
    wa
    #
    wa
    #
    @9
    @10
    crh
    co
    #
    @10
    cbs
    cfv
    #
    @9
    cbs
    cfv
    #
    cmap
    co
    #
    @11
    @12
    @17
    vh
    @18
    @21
    vh
    cv
    #
    @18
    wcel
    @20
    @19
    @22
    wf
    #
    @17
    @22
    @21
    wcel
    #
    @20
    @19
    @9
    @10
    @22
    @20
    eqid
    @19
    eqid
    rhmf
    @17
    @23
    @24
    @17
    @23
    wa
    #
    @24
    @23
    @17
    @23
    simpr
    @19
    cvv
    wcel
    #
    @20
    cvv
    wcel
    #
    wa
    @24
    @23
    wb
    @25
    @26
    @27
    @10
    cbs
    fvex
    @9
    cbs
    fvex
    pm3.2i
    @19
    @20
    @22
    cvv
    cvv
    elmapg
    mp1i
    mpbird
    ex
    syl5
    ssrdv
    @16
    @11
    @18
    wceq
    wph
    @9
    @10
    cR
    cR
    crh
    ovres
    adantl
    @16
    @12
    @21
    wceq
    wph
    @16
    vx
    vy
    @9
    @10
    cR
    cR
    @6
    @21
    @7
    cvv
    @16
    @7
    eqidd
    vx
    va
    weq
    #
    vy
    vb
    weq
    #
    wa
    @6
    @21
    wceq
    @16
    @29
    @28
    @3
    @19
    @5
    @20
    cmap
    @2
    @10
    cbs
    fveq2
    @4
    @9
    cbs
    fveq2
    oveqan12rd
    adantl
    @14
    @15
    simpl
    @14
    @15
    simpr
    @16
    @19
    @20
    cmap
    ovexd
    ovmpt2d
    adantl
    3sstr4d
    ralrimivva
    wph
    va
    vb
    cR
    cR
    @1
    @7
    cvv
    wph
    crh
    crg
    crg
    cxp
    #
    wfn
    #
    @0
    @30
    wss
    #
    @1
    @0
    wfn
    @31
    wph
    rhmfn
    a1i
    wph
    cR
    crg
    wss
    #
    @33
    @32
    wph
    cR
    crg
    cU
    cin
    #
    crg
    rhmsscmap.r
    crg
    cU
    inss1
    syl6eqss
    #
    @35
    cR
    crg
    cR
    crg
    xpss12
    syl2anc
    @30
    @0
    crh
    fnssres
    syl2anc
    @7
    @0
    wfn
    wph
    vx
    vy
    cR
    cR
    @6
    @7
    @7
    eqid
    @3
    @5
    cmap
    ovex
    fnmpt2i
    a1i
    wph
    cR
    @34
    cvv
    rhmsscmap.r
    wph
    @34
    cU
    crg
    cin
    #
    cvv
    crg
    cU
    incom
    wph
    cU
    cV
    wcel
    @36
    cvv
    wcel
    rhmsscmap.u
    cU
    crg
    cV
    inex1g
    syl
    syl5eqel
    eqeltrd
    isssc
    mpbir2and
end
