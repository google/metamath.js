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
include "crg.mm"
include "cin.mm"
include "inss2.mm"
include "syl6eqss.mm"
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
include "fveq2.mm"
include "oveqan12rd.mm"
include "wi.mm"
include "sseld.mm"
include "com12.mm"
include "adantr.mm"
include "impcom.mm"
include "ovexd.mm"
include "ovmpt2d.mm"
include "3sstr4d.mm"
include "ralrimivva.mm"
include "wfn.mm"
include "rhmfn.mm"
include "a1i.mm"
include "inss1.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "fnssres.mm"
include "ovex.mm"
include "fnmpt2i.mm"
include "elex.mm"
include "syl.mm"
include "isssc.mm"
include "mpbir2and.mm"

theorem rhmsscmap
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
  disjoint U x
  disjoint U y
  disjoint ph x
  disjoint ph y
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
  disjoint U a
  disjoint U b
  disjoint k x
  assert |- ( ph -> ( RingHom |` ( R X. R ) ) C_cat ( x e. U , y e. U |-> ( ( Base ` y ) ^m ( Base ` x ) ) ) )

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
    cU
    cU
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
    cU
    wss
    va
    cv
    #
    vb
    cv
    #
    @1
    co
    #
    @8
    @9
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
    wph
    cR
    crg
    cU
    cin
    #
    cU
    rhmsscmap.r
    crg
    cU
    inss2
    syl6eqss
    #
    wph
    @12
    va
    vb
    cR
    cR
    wph
    @8
    cR
    wcel
    #
    @9
    cR
    wcel
    #
    wa
    #
    wa
    #
    @8
    @9
    crh
    co
    #
    @9
    cbs
    cfv
    #
    @8
    cbs
    cfv
    #
    cmap
    co
    #
    @10
    @11
    @18
    vh
    @19
    @22
    vh
    cv
    #
    @19
    wcel
    @21
    @20
    @23
    wf
    #
    @18
    @23
    @22
    wcel
    #
    @21
    @20
    @8
    @9
    @23
    @21
    eqid
    @20
    eqid
    rhmf
    @18
    @24
    @25
    @18
    @24
    wa
    #
    @25
    @24
    @18
    @24
    simpr
    @20
    cvv
    wcel
    #
    @21
    cvv
    wcel
    #
    wa
    @25
    @24
    wb
    @26
    @27
    @28
    @9
    cbs
    fvex
    @8
    cbs
    fvex
    pm3.2i
    @20
    @21
    @23
    cvv
    cvv
    elmapg
    mp1i
    mpbird
    ex
    syl5
    ssrdv
    @17
    @10
    @19
    wceq
    wph
    @8
    @9
    cR
    cR
    crh
    ovres
    adantl
    @18
    vx
    vy
    @8
    @9
    cU
    cU
    @6
    @22
    @7
    cvv
    @18
    @7
    eqidd
    @4
    @8
    wceq
    #
    @2
    @9
    wceq
    #
    wa
    @6
    @22
    wceq
    @18
    @30
    @29
    @3
    @20
    @5
    @21
    cmap
    @2
    @9
    cbs
    fveq2
    @4
    @8
    cbs
    fveq2
    oveqan12rd
    adantl
    @17
    wph
    @8
    cU
    wcel
    #
    @15
    wph
    @31
    wi
    @16
    wph
    @15
    @31
    wph
    cR
    cU
    @8
    @14
    sseld
    com12
    adantr
    impcom
    @17
    wph
    @9
    cU
    wcel
    #
    @16
    wph
    @32
    wi
    @15
    wph
    @16
    @32
    wph
    cR
    cU
    @9
    @14
    sseld
    com12
    adantl
    impcom
    @18
    @20
    @21
    cmap
    ovexd
    ovmpt2d
    3sstr4d
    ralrimivva
    wph
    va
    vb
    cR
    cU
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
    @33
    wss
    #
    @1
    @0
    wfn
    @34
    wph
    rhmfn
    a1i
    wph
    cR
    crg
    wss
    #
    @36
    @35
    wph
    cR
    @13
    crg
    rhmsscmap.r
    crg
    cU
    inss1
    syl6eqss
    #
    @37
    cR
    crg
    cR
    crg
    xpss12
    syl2anc
    @33
    @0
    crh
    fnssres
    syl2anc
    @7
    cU
    cU
    cxp
    wfn
    wph
    vx
    vy
    cU
    cU
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
    cU
    cV
    wcel
    cU
    cvv
    wcel
    rhmsscmap.u
    cU
    cV
    elex
    syl
    isssc
    mpbir2and
end
