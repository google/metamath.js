include "wcel.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wi.mm"
include "wral.mm"
include "pwidg.mm"
include "ad2antrr.mm"
include "0elpw.mm"
include "a1i.mm"
include "simprr.mm"
include "ineq1.mm"
include "eqeq1d.mm"
include "fveq2.mm"
include "ineq1d.mm"
include "imbi12d.mm"
include "ineq2.mm"
include "ineq2d.mm"
include "wb.mm"
include "in0.mm"
include "pm5.5.mm"
include "mp1i.mm"
include "bitrd.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "ex.mm"
include "wss.mm"
include "wf.mm"
include "elmapi.mm"
include "adantl.mm"
include "ffvelrnd.mm"
include "elpwid.mm"
include "simpl.mm"
include "incom.mm"
include "syl6eq.mm"
include "biimpd.mm"
include "cdif.mm"
include "reldisj.mm"
include "difid.mm"
include "sseq2i.mm"
include "ss0.mm"
include "sylbi.mm"
include "syl6com.mm"
include "com13.mm"
include "syl2im.mm"
include "mpdd.mm"

theorem ntrk0kbimka
  let vt: setvar t
  let cB: class B
  let cI: class I
  let cV: class V
  let vs: setvar s

  disjoint B s
  disjoint B t
  disjoint s t
  disjoint I s
  disjoint I t
  assert |- ( ( B e. V /\ I e. ( ~P B ^m ~P B ) ) -> ( ( ( I ` B ) = B /\ A. s e. ~P B A. t e. ~P B ( ( s i^i t ) = (/) -> ( ( I ` s ) i^i ( I ` t ) ) = (/) ) ) -> ( I ` (/) ) = (/) ) )

  proof
    cB
    cV
    wcel
    #
    cI
    cB
    cpw
    #
    @1
    cmap
    co
    wcel
    #
    wa
    #
    cB
    cI
    cfv
    #
    cB
    wceq
    #
    vs
    cv
    #
    vt
    cv
    #
    cin
    #
    c0
    wceq
    #
    @6
    cI
    cfv
    #
    @7
    cI
    cfv
    #
    cin
    #
    c0
    wceq
    #
    wi
    #
    vt
    @1
    wral
    vs
    @1
    wral
    #
    wa
    #
    @4
    c0
    cI
    cfv
    #
    cin
    #
    c0
    wceq
    #
    @17
    c0
    wceq
    #
    @3
    @16
    @19
    @3
    @16
    wa
    #
    cB
    @1
    wcel
    #
    c0
    @1
    wcel
    #
    @15
    @19
    @0
    @22
    @2
    @16
    cB
    cV
    pwidg
    ad2antrr
    @23
    @21
    cB
    0elpw
    #
    a1i
    @3
    @5
    @15
    simprr
    @14
    @19
    cB
    @7
    cin
    #
    c0
    wceq
    #
    @4
    @11
    cin
    #
    c0
    wceq
    #
    wi
    #
    vs
    vt
    cB
    c0
    @1
    @1
    @6
    cB
    wceq
    #
    @9
    @26
    @13
    @28
    @30
    @8
    @25
    c0
    @6
    cB
    @7
    ineq1
    eqeq1d
    @30
    @12
    @27
    c0
    @30
    @10
    @4
    @11
    @6
    cB
    cI
    fveq2
    ineq1d
    eqeq1d
    imbi12d
    @7
    c0
    wceq
    #
    @29
    cB
    c0
    cin
    #
    c0
    wceq
    #
    @19
    wi
    #
    @19
    @31
    @26
    @33
    @28
    @19
    @31
    @25
    @32
    c0
    @7
    c0
    cB
    ineq2
    eqeq1d
    @31
    @27
    @18
    c0
    @31
    @11
    @17
    @4
    @7
    c0
    cI
    fveq2
    ineq2d
    eqeq1d
    imbi12d
    @33
    @34
    @19
    wb
    @31
    cB
    in0
    @33
    @19
    pm5.5
    mp1i
    bitrd
    rspc2va
    syl21anc
    ex
    @3
    @17
    cB
    wss
    #
    @16
    @5
    @19
    @20
    wi
    @3
    @17
    cB
    @3
    @1
    @1
    c0
    cI
    @2
    @1
    @1
    cI
    wf
    @0
    cI
    @1
    @1
    elmapi
    adantl
    @23
    @3
    @24
    a1i
    ffvelrnd
    elpwid
    @5
    @15
    simpl
    @19
    @5
    @35
    @20
    @5
    @19
    @17
    cB
    cin
    #
    c0
    wceq
    #
    @35
    @20
    wi
    @5
    @19
    @37
    @5
    @18
    @36
    c0
    @5
    @18
    cB
    @17
    cin
    @36
    @4
    cB
    @17
    ineq1
    cB
    @17
    incom
    syl6eq
    eqeq1d
    biimpd
    @35
    @37
    @17
    cB
    cB
    cdif
    #
    wss
    #
    @20
    @35
    @37
    @39
    @17
    cB
    cB
    reldisj
    biimpd
    @39
    @17
    c0
    wss
    @20
    @38
    c0
    @17
    cB
    difid
    sseq2i
    @17
    ss0
    sylbi
    syl6com
    syl6com
    com13
    syl2im
    mpdd
end
