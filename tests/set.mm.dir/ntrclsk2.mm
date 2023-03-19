include "cv.mm"
include "cfv.mm"
include "wss.mm"
include "cpw.mm"
include "wral.mm"
include "weq.mm"
include "fveq2.mm"
include "id.mm"
include "sseq12d.mm"
include "cbvralv.mm"
include "cdif.mm"
include "wcel.mm"
include "ntrclsrcomplex.mm"
include "adantr.mm"
include "wa.mm"
include "wceq.mm"
include "wb.mm"
include "difeq2.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "elpwi.mm"
include "dfss4.mm"
include "sylib.mm"
include "eqcomd.mm"
include "rspcedvd.mm"
include "w3a.mm"
include "3ad2ant3.mm"
include "wf.mm"
include "cmap.mm"
include "co.mm"
include "ntrclsiex.mm"
include "elmapi.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "ffvelrnd.mm"
include "elpwid.mm"
include "difssd.mm"
include "sscon34b.mm"
include "syl2anc.mm"
include "simp2.mm"
include "sseq1d.mm"
include "bitrd.mm"
include "cvv.mm"
include "ntrclsbex.mm"
include "eqid.mm"
include "dssmapfv3d.mm"
include "sseq2d.mm"
include "ntrclsfv1.mm"
include "fveq1d.mm"
include "3bitr2d.mm"
include "ralxfrd2.mm"
include "syl5bb.mm"

theorem ntrclsk2
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
  assert |- ( ph -> ( A. s e. ~P B ( I ` s ) C_ s <-> A. s e. ~P B s C_ ( K ` s ) ) )

  proof
    vs
    cv
    #
    cI
    cfv
    #
    @0
    wss
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
    @4
    wss
    #
    vt
    @3
    wral
    wph
    @0
    @0
    cK
    cfv
    #
    wss
    #
    vs
    @3
    wral
    @2
    @6
    vs
    vt
    @3
    vs
    vt
    weq
    #
    @1
    @5
    @0
    @4
    @0
    @4
    cI
    fveq2
    @9
    id
    sseq12d
    cbvralv
    wph
    @6
    @8
    vt
    vs
    cB
    @0
    cdif
    #
    @3
    @3
    wph
    @10
    @3
    wcel
    #
    @0
    @3
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
    @4
    @3
    wcel
    #
    wa
    #
    @4
    @10
    wceq
    #
    @4
    cB
    cB
    @4
    cdif
    #
    cdif
    #
    wceq
    #
    vs
    @17
    @3
    wph
    @17
    @3
    wcel
    @14
    wph
    cB
    cD
    @4
    cI
    cK
    cO
    ntrcls.d
    ntrcls.r
    ntrclsrcomplex
    adantr
    @0
    @17
    wceq
    #
    @16
    @19
    wb
    @15
    @20
    @10
    @18
    @4
    @0
    @17
    cB
    difeq2
    eqeq2d
    adantl
    @15
    @18
    @4
    @14
    @18
    @4
    wceq
    #
    wph
    @14
    @4
    cB
    wss
    @21
    @4
    cB
    elpwi
    @4
    cB
    dfss4
    sylib
    adantl
    eqcomd
    rspcedvd
    wph
    @12
    @16
    w3a
    #
    @6
    @10
    cI
    cfv
    #
    @10
    wss
    #
    @8
    @16
    wph
    @6
    @24
    wb
    @12
    @16
    @5
    @23
    @4
    @10
    @4
    @10
    cI
    fveq2
    @16
    id
    sseq12d
    3ad2ant3
    @22
    @24
    @0
    cB
    @23
    cdif
    #
    wss
    #
    @0
    @0
    cI
    cD
    cfv
    #
    cfv
    #
    wss
    #
    @8
    @22
    @24
    cB
    @10
    cdif
    #
    @25
    wss
    #
    @26
    @22
    @23
    cB
    wss
    @10
    cB
    wss
    @24
    @31
    wb
    @22
    @23
    cB
    @22
    @3
    @3
    @10
    cI
    wph
    @12
    @3
    @3
    cI
    wf
    #
    @16
    wph
    cI
    @3
    @3
    cmap
    co
    wcel
    #
    @32
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
    #
    cI
    @3
    @3
    elmapi
    syl
    3ad2ant1
    wph
    @12
    @11
    @16
    @13
    3ad2ant1
    ffvelrnd
    elpwid
    @22
    cB
    @0
    difssd
    @23
    @10
    cB
    sscon34b
    syl2anc
    @22
    @12
    @31
    @26
    wb
    wph
    @12
    @16
    simp2
    #
    @12
    @30
    @0
    @25
    @12
    @0
    cB
    wss
    @30
    @0
    wceq
    @0
    cB
    elpwi
    @0
    cB
    dfss4
    sylib
    sseq1d
    syl
    bitrd
    @22
    @28
    @25
    @0
    @22
    cB
    cD
    @0
    @28
    vk
    cI
    @27
    cO
    cvv
    vj
    vi
    ntrcls.o
    ntrcls.d
    wph
    @12
    cB
    cvv
    wcel
    @16
    wph
    cB
    cD
    cI
    cK
    cO
    ntrcls.d
    ntrcls.r
    ntrclsbex
    3ad2ant1
    wph
    @12
    @33
    @16
    @34
    3ad2ant1
    @27
    eqid
    @35
    @28
    eqid
    dssmapfv3d
    sseq2d
    wph
    @12
    @29
    @8
    wb
    @16
    wph
    @28
    @7
    @0
    wph
    @0
    @27
    cK
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
    ntrclsfv1
    fveq1d
    sseq2d
    3ad2ant1
    3bitr2d
    bitrd
    ralxfrd2
    syl5bb
end
