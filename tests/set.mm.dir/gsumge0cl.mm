include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cxr.mm"
include "cin.mm"
include "cbs.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "iccssxr.mm"
include "df-ss.mm"
include "mpbi.mm"
include "eqcomi.mm"
include "cvv.mm"
include "wcel.mm"
include "ovex.mm"
include "cxrs.mm"
include "xrsbas.mm"
include "ressbas.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "cmnf.mm"
include "csn.mm"
include "cdif.mm"
include "cress.mm"
include "cmnd.mm"
include "wa.mm"
include "c0g.mm"
include "ccmn.mm"
include "eqid.mm"
include "xrs1cmn.mm"
include "cmnmnd.mm"
include "xrge0cmn.mm"
include "eqeltri.mm"
include "pm3.2i.mm"
include "cv.mm"
include "wral.mm"
include "sseli.mm"
include "wne.mm"
include "wn.mm"
include "mnfxr.mm"
include "a1i.mm"
include "0xr.mm"
include "clt.mm"
include "wbr.mm"
include "mnflt0.mm"
include "cle.mm"
include "pnfxr.mm"
include "id.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "xrltletrd.mm"
include "xrgtned.mm"
include "nelsn.mm"
include "syl.mm"
include "eldifd.mm"
include "rgen.mm"
include "dfss3.mm"
include "mpbir.mm"
include "0e0iccpnf.mm"
include "difss.mm"
include "ressbas2.mm"
include "xrs10.mm"
include "xrex.mm"
include "difexg.mm"
include "simpli.mm"
include "ressabs.mm"
include "mp2an.mm"
include "eqtr2i.mm"
include "submnd0.mm"
include "gsumcl.mm"

theorem gsumge0cl
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cV: class V
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume gsumge0cl.1: |- G = ( RR*s |`s ( 0 [,] +oo ) )
  assume gsumge0cl.2: |- ( ph -> X e. V )
  assume gsumge0cl.3: |- ( ph -> F : X --> ( 0 [,] +oo ) )
  assume gsumge0cl.4: |- ( ph -> F finSupp 0 )


  assert |- ( ph -> ( G gsum F ) e. ( 0 [,] +oo ) )

  proof
    wph
    cX
    cc0
    cpnf
    cicc
    co
    #
    cF
    cG
    cV
    cc0
    @0
    @0
    cxr
    cin
    #
    cG
    cbs
    cfv
    #
    @1
    @0
    @0
    cxr
    wss
    @1
    @0
    wceq
    cc0
    cpnf
    iccssxr
    #
    @0
    cxr
    df-ss
    mpbi
    eqcomi
    @0
    cvv
    wcel
    @1
    @2
    wceq
    cc0
    cpnf
    cicc
    ovex
    @0
    cxr
    cG
    cvv
    cxrs
    gsumge0cl.1
    xrsbas
    ressbas
    ax-mp
    eqtri
    cxrs
    cxr
    cmnf
    csn
    #
    cdif
    #
    cress
    co
    #
    cmnd
    wcel
    #
    cG
    cmnd
    wcel
    #
    wa
    @0
    @5
    wss
    #
    cc0
    @0
    wcel
    #
    wa
    cc0
    cG
    c0g
    cfv
    wceq
    @7
    @8
    @6
    ccmn
    wcel
    @7
    @6
    @6
    eqid
    #
    xrs1cmn
    @6
    cmnmnd
    ax-mp
    cG
    ccmn
    wcel
    #
    @8
    cG
    cxrs
    @0
    cress
    co
    #
    ccmn
    gsumge0cl.1
    xrge0cmn
    eqeltri
    #
    cG
    cmnmnd
    ax-mp
    pm3.2i
    @9
    @10
    @9
    vx
    cv
    #
    @5
    wcel
    #
    vx
    @0
    wral
    @16
    vx
    @0
    @15
    @0
    wcel
    #
    @15
    cxr
    @4
    @0
    cxr
    @15
    @3
    sseli
    #
    @17
    @15
    cmnf
    wne
    @15
    @4
    wcel
    wn
    @17
    cmnf
    @15
    cmnf
    cxr
    wcel
    @17
    mnfxr
    a1i
    #
    @18
    @17
    cmnf
    cc0
    @15
    @19
    cc0
    cxr
    wcel
    #
    @17
    0xr
    a1i
    #
    @18
    cmnf
    cc0
    clt
    wbr
    @17
    mnflt0
    a1i
    @17
    @20
    cpnf
    cxr
    wcel
    #
    @17
    cc0
    @15
    cle
    wbr
    @21
    @22
    @17
    pnfxr
    a1i
    @17
    id
    cc0
    cpnf
    @15
    iccgelb
    syl3anc
    xrltletrd
    xrgtned
    @15
    cmnf
    nelsn
    syl
    eldifd
    rgen
    vx
    @0
    @5
    dfss3
    mpbir
    0e0iccpnf
    pm3.2i
    #
    @5
    @0
    @6
    cG
    cc0
    @5
    cxr
    wss
    @5
    @6
    cbs
    cfv
    wceq
    cxr
    @4
    difss
    @5
    cxr
    @6
    cxrs
    @11
    xrsbas
    ressbas2
    ax-mp
    @6
    @11
    xrs10
    @6
    @0
    cress
    co
    #
    @13
    cG
    @5
    cvv
    wcel
    #
    @9
    @24
    @13
    wceq
    cxr
    cvv
    wcel
    @25
    xrex
    cxr
    @4
    cvv
    difexg
    ax-mp
    @9
    @10
    @23
    simpli
    @5
    @0
    cxrs
    cvv
    ressabs
    mp2an
    cG
    @13
    gsumge0cl.1
    eqcomi
    eqtr2i
    submnd0
    mp2an
    @12
    wph
    @14
    a1i
    gsumge0cl.2
    gsumge0cl.3
    gsumge0cl.4
    gsumcl
end
