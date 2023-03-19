include "cufil.mm"
include "cfv.mm"
include "wcel.mm"
include "ccld.mm"
include "cun.mm"
include "cpw.mm"
include "cv.mm"
include "wo.mm"
include "wss.mm"
include "cuni.mm"
include "elssuni.mm"
include "c0.mm"
include "csn.mm"
include "unieqi.mm"
include "uniun.mm"
include "0ex.mm"
include "unisn.mm"
include "uneq2i.mm"
include "un0.mm"
include "3eqtri.mm"
include "eqtr2i.mm"
include "cfil.mm"
include "wceq.mm"
include "ufilfil.mm"
include "filunibas.mm"
include "syl.mm"
include "syl5reqr.mm"
include "sseq2d.mm"
include "syl5ibr.mm"
include "eqid.mm"
include "cldss.mm"
include "jaod.mm"
include "wa.mm"
include "cdif.mm"
include "ufilss.mm"
include "ssun1.mm"
include "sseqtr4i.mm"
include "a1i.mm"
include "sseld.mm"
include "ctop.mm"
include "wb.mm"
include "cconn.mm"
include "filconn.mm"
include "conntop.mm"
include "3syl.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "biimpa.mm"
include "iscld2.mm"
include "syl2anc.mm"
include "difeq1d.mm"
include "eleq1d.mm"
include "bitr4d.mm"
include "sylibrd.mm"
include "orim12d.mm"
include "mpd.mm"
include "ex.mm"
include "impbid.mm"
include "elun.mm"
include "selpw.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem ufildr
  let cF: class F
  let cJ: class J
  let cX: class X
  let vx: setvar x
  assume ufildr.1: |- J = ( F u. { (/) } )


  assert |- ( F e. ( UFil ` X ) -> ( J u. ( Clsd ` J ) ) = ~P X )

  proof
    cF
    cX
    cufil
    cfv
    wcel
    #
    vx
    cJ
    cJ
    ccld
    cfv
    #
    cun
    #
    cX
    cpw
    #
    @0
    vx
    cv
    #
    cJ
    wcel
    #
    @4
    @1
    wcel
    #
    wo
    #
    @4
    cX
    wss
    #
    @4
    @2
    wcel
    @4
    @3
    wcel
    @0
    @7
    @8
    @0
    @5
    @8
    @6
    @5
    @8
    @0
    @4
    cJ
    cuni
    #
    wss
    #
    @4
    cJ
    elssuni
    @0
    cX
    @9
    @4
    @0
    @9
    cF
    cuni
    #
    cX
    @9
    cF
    c0
    csn
    #
    cun
    #
    cuni
    #
    @11
    cJ
    @13
    ufildr.1
    unieqi
    @14
    @11
    @12
    cuni
    #
    cun
    @11
    c0
    cun
    @11
    cF
    @12
    uniun
    @15
    c0
    @11
    c0
    0ex
    unisn
    uneq2i
    @11
    un0
    3eqtri
    eqtr2i
    @0
    cF
    cX
    cfil
    cfv
    wcel
    #
    @11
    cX
    wceq
    cF
    cX
    ufilfil
    #
    cF
    cX
    filunibas
    syl
    syl5reqr
    #
    sseq2d
    #
    syl5ibr
    @6
    @8
    @0
    @10
    @4
    cJ
    @9
    @9
    eqid
    #
    cldss
    @19
    syl5ibr
    jaod
    @0
    @8
    @7
    @0
    @8
    wa
    #
    @4
    cF
    wcel
    #
    cX
    @4
    cdif
    #
    cF
    wcel
    #
    wo
    @7
    @4
    cF
    cX
    ufilss
    @21
    @22
    @5
    @24
    @6
    @21
    cF
    cJ
    @4
    cF
    cJ
    wss
    @21
    cF
    @13
    cJ
    cF
    @12
    ssun1
    ufildr.1
    sseqtr4i
    a1i
    #
    sseld
    @21
    @24
    @23
    cJ
    wcel
    #
    @6
    @21
    cF
    cJ
    @23
    @25
    sseld
    @21
    @6
    @9
    @4
    cdif
    #
    cJ
    wcel
    #
    @26
    @21
    cJ
    ctop
    wcel
    #
    @10
    @6
    @28
    wb
    @0
    @29
    @8
    @0
    cJ
    @13
    ctop
    ufildr.1
    @0
    @16
    @13
    cconn
    wcel
    @13
    ctop
    wcel
    @17
    cF
    cX
    filconn
    @13
    conntop
    3syl
    syl5eqel
    adantr
    @0
    @8
    @10
    @19
    biimpa
    @4
    cJ
    @9
    @20
    iscld2
    syl2anc
    @0
    @26
    @28
    wb
    @8
    @0
    @23
    @27
    cJ
    @0
    cX
    @9
    @4
    @18
    difeq1d
    eleq1d
    adantr
    bitr4d
    sylibrd
    orim12d
    mpd
    ex
    impbid
    @4
    cJ
    @1
    elun
    vx
    cX
    selpw
    3bitr4g
    eqrdv
end
