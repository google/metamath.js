include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cpw.mm"
include "wral.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "cbvralv.mm"
include "cdif.mm"
include "wcel.mm"
include "ntrclsrcomplex.mm"
include "adantr.mm"
include "wa.mm"
include "wb.mm"
include "difeq2.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "wss.mm"
include "elpwi.mm"
include "dfss4.mm"
include "sylib.mm"
include "eqcomd.mm"
include "rspcedvd.mm"
include "w3a.mm"
include "3ad2ant3.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "ntrclsiex.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "elpwid.mm"
include "rcompleq.mm"
include "syl2anc.mm"
include "wbr.mm"
include "ntrclsnvobr.mm"
include "ffvelrnda.mm"
include "ntrclsfv.mm"
include "simpr.mm"
include "difeq2d.mm"
include "eqtrd.mm"
include "bitr4d.mm"
include "3adant3.mm"
include "bitrd.mm"
include "ralxfrd2.mm"
include "syl5bb.mm"

theorem ntrclsk4
  let wph: wff ph
  let cB: class B
  let cD: class D
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cI: class I
  let cK: class K
  let cO: class O
  let vs: setvar s
  let vt: setvar t
  assume ntrcls.o: |- O = ( i e. _V |-> ( k e. ( ~P i ^m ~P i ) |-> ( j e. ~P i |-> ( i \ ( k ` ( i \ j ) ) ) ) ) )
  assume ntrcls.d: |- D = ( O ` B )
  assume ntrcls.r: |- ( ph -> I D K )

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B s
  disjoint i j
  disjoint i k
  disjoint i s
  disjoint j k
  disjoint j s
  disjoint k s
  disjoint I j
  disjoint I k
  disjoint I s
  disjoint K j
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint ph s
  disjoint B t
  disjoint i t
  disjoint j t
  disjoint k t
  disjoint s t
  disjoint I t
  disjoint K t
  disjoint ph t
  assert |- ( ph -> ( A. s e. ~P B ( I ` ( I ` s ) ) = ( I ` s ) <-> A. s e. ~P B ( K ` ( K ` s ) ) = ( K ` s ) ) )

  proof
    vs
    cv
    #
    cI
    cfv
    #
    cI
    cfv
    #
    @1
    wceq
    #
    vs
    cB
    cpw
    #
    wral
    vt
    cv
    #
    cI
    cfv
    #
    cI
    cfv
    #
    @6
    wceq
    #
    vt
    @4
    wral
    wph
    @0
    cK
    cfv
    #
    cK
    cfv
    #
    @9
    wceq
    #
    vs
    @4
    wral
    @3
    @8
    vs
    vt
    @4
    vs
    vt
    weq
    #
    @2
    @7
    @1
    @6
    @12
    @1
    @6
    cI
    @0
    @5
    cI
    fveq2
    #
    fveq2d
    @13
    eqeq12d
    cbvralv
    wph
    @8
    @11
    vt
    vs
    cB
    @0
    cdif
    #
    @4
    @4
    wph
    @14
    @4
    wcel
    @0
    @4
    wcel
    #
    wph
    cB
    cD
    @0
    cI
    cK
    cO
    ntrcls.d
    ntrcls.r
    ntrclsrcomplex
    #
    adantr
    wph
    @5
    @4
    wcel
    #
    wa
    #
    @5
    @14
    wceq
    #
    @5
    cB
    cB
    @5
    cdif
    #
    cdif
    #
    wceq
    #
    vs
    @20
    @4
    wph
    @20
    @4
    wcel
    @17
    wph
    cB
    cD
    @5
    cI
    cK
    cO
    ntrcls.d
    ntrcls.r
    ntrclsrcomplex
    adantr
    @0
    @20
    wceq
    #
    @19
    @22
    wb
    @18
    @23
    @14
    @21
    @5
    @0
    @20
    cB
    difeq2
    eqeq2d
    adantl
    @17
    @22
    wph
    @17
    @21
    @5
    @17
    @5
    cB
    wss
    @21
    @5
    wceq
    @5
    cB
    elpwi
    @5
    cB
    dfss4
    sylib
    eqcomd
    adantl
    rspcedvd
    wph
    @15
    @19
    w3a
    @8
    @14
    cI
    cfv
    #
    cI
    cfv
    #
    @24
    wceq
    #
    @11
    @19
    wph
    @8
    @26
    wb
    @15
    @19
    @7
    @25
    @6
    @24
    @19
    @6
    @24
    cI
    @5
    @14
    cI
    fveq2
    #
    fveq2d
    @27
    eqeq12d
    3ad2ant3
    wph
    @15
    @26
    @11
    wb
    @19
    wph
    @15
    wa
    #
    @26
    cB
    @25
    cdif
    #
    cB
    @24
    cdif
    #
    wceq
    #
    @11
    wph
    @26
    @31
    wb
    #
    @15
    wph
    @25
    cB
    wss
    @24
    cB
    wss
    #
    @32
    wph
    @25
    cB
    wph
    @4
    @4
    @24
    cI
    wph
    cI
    @4
    @4
    cmap
    co
    #
    wcel
    @4
    @4
    cI
    wf
    wph
    cB
    cD
    vi
    vj
    vk
    cI
    cK
    cO
    ntrcls.o
    ntrcls.d
    ntrcls.r
    ntrclsiex
    cI
    @4
    @4
    elmapi
    syl
    #
    wph
    @4
    @4
    @14
    cI
    @35
    @16
    ffvelrnd
    #
    ffvelrnd
    elpwid
    wph
    @24
    cB
    @36
    elpwid
    #
    @25
    @24
    cB
    rcompleq
    syl2anc
    adantr
    @28
    @10
    @29
    @9
    @30
    @28
    @10
    cB
    cB
    @9
    cdif
    #
    cI
    cfv
    #
    cdif
    @29
    @28
    cB
    cD
    @9
    vi
    vj
    vk
    cK
    cI
    cO
    ntrcls.o
    ntrcls.d
    wph
    cK
    cI
    cD
    wbr
    @15
    wph
    cB
    cD
    vi
    vj
    vk
    cI
    cK
    cO
    ntrcls.o
    ntrcls.d
    ntrcls.r
    ntrclsnvobr
    #
    adantr
    #
    wph
    @4
    @4
    @0
    cK
    wph
    cK
    @34
    wcel
    @4
    @4
    cK
    wf
    wph
    cB
    cD
    vi
    vj
    vk
    cK
    cI
    cO
    ntrcls.o
    ntrcls.d
    @40
    ntrclsiex
    cK
    @4
    @4
    elmapi
    syl
    ffvelrnda
    ntrclsfv
    @28
    @39
    @25
    cB
    @28
    @38
    @24
    cI
    @28
    @38
    cB
    @30
    cdif
    #
    @24
    @28
    @9
    @30
    cB
    @28
    cB
    cD
    @0
    vi
    vj
    vk
    cK
    cI
    cO
    ntrcls.o
    ntrcls.d
    @41
    wph
    @15
    simpr
    ntrclsfv
    #
    difeq2d
    wph
    @42
    @24
    wceq
    #
    @15
    wph
    @33
    @44
    @37
    @24
    cB
    dfss4
    sylib
    adantr
    eqtrd
    fveq2d
    difeq2d
    eqtrd
    @43
    eqeq12d
    bitr4d
    3adant3
    bitrd
    ralxfrd2
    syl5bb
end
