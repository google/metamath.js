include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cpw.mm"
include "cxp.mm"
include "ccda.mm"
include "co.mm"
include "cv.mm"
include "cmap.mm"
include "ciun.mm"
include "pwfseq.mm"
include "wi.mm"
include "c1o.mm"
include "c2o.mm"
include "cun.mm"
include "cen.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "oveq1.mm"
include "id.mm"
include "breq12d.mm"
include "csn.mm"
include "df1o2.mm"
include "oveq2i.mm"
include "vex.mm"
include "0ex.mm"
include "mapsnen.mm"
include "eqbrtri.mm"
include "vtoclg.mm"
include "ensym.mm"
include "3syl.mm"
include "map2xp.mm"
include "wn.mm"
include "wa.mm"
include "cdm.mm"
include "wf.mm"
include "elmapi.mm"
include "fdm.mm"
include "syl.mm"
include "adantr.mm"
include "csuc.mm"
include "1onn.mm"
include "elexi.mm"
include "sucid.mm"
include "df-2o.mm"
include "eleqtrri.mm"
include "1on.mm"
include "onirri.mm"
include "nelneq2.mm"
include "mp2an.mm"
include "adantl.mm"
include "eqeq1d.mm"
include "mtbiri.mm"
include "pm2.65i.mm"
include "elin.mm"
include "mtbir.mm"
include "a1i.mm"
include "eq0rdv.mm"
include "cdaenun.mm"
include "syl3anc.mm"
include "wss.mm"
include "omex.mm"
include "ovex.mm"
include "iunex.mm"
include "oveq2.mm"
include "ssiun2s.mm"
include "ax-mp.mm"
include "2onn.mm"
include "unssi.mm"
include "ssdomg.mm"
include "mp2.mm"
include "endomtr.mm"
include "sylancl.mm"
include "domtr.mm"
include "expcom.mm"
include "mtod.mm"

theorem pwxpndom2
  let cA: class A
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( _om ~<_ A -> -. ~P A ~<_ ( A +c ( A X. A ) ) )

  proof
    com
    cA
    cdom
    wbr
    #
    cA
    cpw
    #
    cA
    cA
    cA
    cxp
    #
    ccda
    co
    #
    cdom
    wbr
    #
    @1
    vn
    com
    cA
    vn
    cv
    #
    cmap
    co
    #
    ciun
    #
    cdom
    wbr
    #
    cA
    vn
    pwfseq
    @0
    @3
    @7
    cdom
    wbr
    #
    @4
    @8
    wi
    @0
    @3
    cA
    c1o
    cmap
    co
    #
    cA
    c2o
    cmap
    co
    #
    cun
    #
    cen
    wbr
    #
    @12
    @7
    cdom
    wbr
    #
    @9
    @0
    cA
    @10
    cen
    wbr
    #
    @2
    @11
    cen
    wbr
    #
    @10
    @11
    cin
    #
    c0
    wceq
    @13
    @0
    cA
    cvv
    wcel
    #
    @10
    cA
    cen
    wbr
    #
    @15
    com
    cA
    cdom
    reldom
    brrelex2i
    #
    vx
    cv
    #
    c1o
    cmap
    co
    #
    @21
    cen
    wbr
    @19
    vx
    cA
    cvv
    @21
    cA
    wceq
    #
    @22
    @10
    @21
    cA
    cen
    @21
    cA
    c1o
    cmap
    oveq1
    @23
    id
    breq12d
    @22
    @21
    c0
    csn
    #
    cmap
    co
    @21
    cen
    c1o
    @24
    @21
    cmap
    df1o2
    oveq2i
    @21
    c0
    vx
    vex
    0ex
    mapsnen
    eqbrtri
    vtoclg
    @10
    cA
    ensym
    3syl
    @0
    @18
    @11
    @2
    cen
    wbr
    @16
    @20
    cA
    cvv
    map2xp
    @11
    @2
    ensym
    3syl
    @0
    vx
    @17
    @21
    @17
    wcel
    #
    wn
    @0
    @25
    @21
    @10
    wcel
    #
    @21
    @11
    wcel
    #
    wa
    #
    @28
    @21
    cdm
    #
    c1o
    wceq
    #
    @26
    @30
    @27
    @26
    c1o
    cA
    @21
    wf
    @30
    @21
    cA
    c1o
    elmapi
    c1o
    cA
    @21
    fdm
    syl
    adantr
    @28
    @30
    c2o
    c1o
    wceq
    #
    c1o
    c2o
    wcel
    c1o
    c1o
    wcel
    wn
    @31
    wn
    c1o
    c1o
    csuc
    c2o
    c1o
    c1o
    com
    1onn
    elexi
    sucid
    df-2o
    eleqtrri
    c1o
    1on
    onirri
    c1o
    c2o
    c1o
    nelneq2
    mp2an
    @28
    @29
    c2o
    c1o
    @27
    @29
    c2o
    wceq
    #
    @26
    @27
    c2o
    cA
    @21
    wf
    @32
    @21
    cA
    c2o
    elmapi
    c2o
    cA
    @21
    fdm
    syl
    adantl
    eqeq1d
    mtbiri
    pm2.65i
    @21
    @10
    @11
    elin
    mtbir
    a1i
    eq0rdv
    cA
    @10
    @2
    @11
    cdaenun
    syl3anc
    @7
    cvv
    wcel
    @12
    @7
    wss
    @14
    vn
    com
    @6
    omex
    cA
    @5
    cmap
    ovex
    iunex
    @10
    @11
    @7
    c1o
    com
    wcel
    @10
    @7
    wss
    1onn
    vn
    com
    @6
    c1o
    @10
    @5
    c1o
    cA
    cmap
    oveq2
    ssiun2s
    ax-mp
    c2o
    com
    wcel
    @11
    @7
    wss
    2onn
    vn
    com
    @6
    c2o
    @11
    @5
    c2o
    cA
    cmap
    oveq2
    ssiun2s
    ax-mp
    unssi
    @12
    @7
    cvv
    ssdomg
    mp2
    @3
    @12
    @7
    endomtr
    sylancl
    @4
    @9
    @8
    @1
    @3
    @7
    domtr
    expcom
    syl
    mtod
end
