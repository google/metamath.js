include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "cfg.mm"
include "cfbas.mm"
include "wss.mm"
include "cpw.mm"
include "cdif.mm"
include "wn.mm"
include "filfbas.mm"
include "fbncp.mm"
include "sylan.mm"
include "wb.mm"
include "filelss.mm"
include "trfil3.mm"
include "syldan.mm"
include "mpbird.mm"
include "syl.mm"
include "restsspw.mm"
include "sspwb.mm"
include "sylib.mm"
include "syl5ss.mm"
include "filtop.mm"
include "adantr.mm"
include "fbasweak.mm"
include "syl3anc.mm"
include "trfilss.mm"
include "fgss.mm"
include "wceq.mm"
include "fgfil.mm"
include "sseqtrd.mm"
include "cv.mm"
include "wrex.mm"
include "wi.mm"
include "ex.mm"
include "cin.mm"
include "elrestr.mm"
include "3expa.mm"
include "inss1.mm"
include "sseq1.mm"
include "rspcev.mm"
include "sylancl.mm"
include "jcad.mm"
include "elfg.mm"
include "sylibrd.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem fgtr
  let cA: class A
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cV: class V


  assert |- ( ( F e. ( Fil ` X ) /\ A e. F ) -> ( X filGen ( F |`t A ) ) = F )

  proof
    cF
    cX
    cfil
    cfv
    #
    wcel
    #
    cA
    cF
    wcel
    #
    wa
    #
    cX
    cF
    cA
    crest
    co
    #
    cfg
    co
    #
    cF
    @3
    @5
    cX
    cF
    cfg
    co
    #
    cF
    @3
    @4
    cX
    cfbas
    cfv
    #
    wcel
    #
    cF
    @7
    wcel
    #
    @4
    cF
    wss
    @5
    @6
    wss
    @3
    @4
    cA
    cfbas
    cfv
    wcel
    #
    @4
    cX
    cpw
    #
    wss
    cX
    cF
    wcel
    #
    @8
    @3
    @4
    cA
    cfil
    cfv
    wcel
    #
    @10
    @3
    @13
    cX
    cA
    cdif
    cF
    wcel
    wn
    #
    @1
    @9
    @2
    @14
    cF
    cX
    filfbas
    #
    cA
    cX
    cF
    cX
    fbncp
    sylan
    @1
    @2
    cA
    cX
    wss
    #
    @13
    @14
    wb
    cA
    cF
    cX
    filelss
    #
    cA
    cF
    cX
    trfil3
    syldan
    mpbird
    @4
    cA
    filfbas
    syl
    @3
    @4
    cA
    cpw
    #
    @11
    cA
    cF
    restsspw
    @3
    @16
    @18
    @11
    wss
    @17
    cA
    cX
    sspwb
    sylib
    syl5ss
    @1
    @12
    @2
    cF
    cX
    filtop
    adantr
    @4
    cF
    cA
    cX
    fbasweak
    syl3anc
    #
    @1
    @9
    @2
    @15
    adantr
    cA
    cF
    cX
    trfilss
    @4
    cF
    cX
    fgss
    syl3anc
    @1
    @6
    cF
    wceq
    @2
    cF
    cX
    fgfil
    adantr
    sseqtrd
    @3
    vx
    cF
    @5
    @3
    vx
    cv
    #
    cF
    wcel
    #
    @20
    cX
    wss
    #
    vy
    cv
    #
    @20
    wss
    #
    vy
    @4
    wrex
    #
    wa
    #
    @20
    @5
    wcel
    #
    @3
    @21
    @22
    @25
    @1
    @21
    @22
    wi
    @2
    @1
    @21
    @22
    @20
    cF
    cX
    filelss
    ex
    adantr
    @3
    @21
    @25
    @3
    @21
    wa
    @20
    cA
    cin
    #
    @4
    wcel
    #
    @28
    @20
    wss
    #
    @25
    @1
    @2
    @21
    @29
    @20
    cA
    cF
    @0
    cF
    elrestr
    3expa
    @20
    cA
    inss1
    @24
    @30
    vy
    @28
    @4
    @23
    @28
    @20
    sseq1
    rspcev
    sylancl
    ex
    jcad
    @3
    @8
    @27
    @26
    wb
    @19
    vy
    @20
    @4
    cX
    elfg
    syl
    sylibrd
    ssrdv
    eqssd
end
