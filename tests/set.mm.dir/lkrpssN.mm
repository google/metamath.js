include "cfv.mm"
include "wpss.mm"
include "cbs.mm"
include "wne.mm"
include "wceq.mm"
include "wa.mm"
include "wss.mm"
include "df-pss.mm"
include "simpr.mm"
include "eqid.mm"
include "clvec.mm"
include "wcel.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "lkrssv.mm"
include "adantr.mm"
include "psssstrd.mm"
include "pssned.mm"
include "sylan2br.mm"
include "clsh.mm"
include "wn.mm"
include "simplr.mm"
include "ad2antrr.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "eqsstr3d.mm"
include "eqssd.mm"
include "wb.mm"
include "lkrshp4.mm"
include "necon1bbid.mm"
include "mpbird.mm"
include "pm2.21dd.mm"
include "wo.mm"
include "lkrshpor.mm"
include "mpjaodan.mm"
include "lshpcmp.mm"
include "mpbid.mm"
include "ex.mm"
include "necon3ad.mm"
include "impr.mm"
include "jca.mm"
include "simprr.mm"
include "eqcomd.mm"
include "sseqtrd.mm"
include "simprl.mm"
include "neeqtrd.mm"
include "impbida.mm"
include "syl5bb.mm"
include "lkr0f2.mm"
include "necon3bid.mm"
include "anbi12d.mm"
include "bitrd.mm"

theorem lkrpssN
  let wph: wff ph
  let cD: class D
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let c.0: class .0.
  assume lkrpss.f: |- F = ( LFnl ` W )
  assume lkrpss.k: |- K = ( LKer ` W )
  assume lkrpss.d: |- D = ( LDual ` W )
  assume lkrpss.o: |- .0. = ( 0g ` D )
  assume lkrpss.w: |- ( ph -> W e. LVec )
  assume lkrpss.g: |- ( ph -> G e. F )
  assume lkrpss.h: |- ( ph -> H e. F )


  assert |- ( ph -> ( ( K ` G ) C. ( K ` H ) <-> ( G =/= .0. /\ H = .0. ) ) )

  proof
    wph
    cG
    cK
    cfv
    #
    cH
    cK
    cfv
    #
    wpss
    #
    @0
    cW
    cbs
    cfv
    #
    wne
    #
    @1
    @3
    wceq
    #
    wa
    #
    cG
    c.0
    wne
    #
    cH
    c.0
    wceq
    #
    wa
    @2
    @0
    @1
    wss
    #
    @0
    @1
    wne
    #
    wa
    #
    wph
    @6
    @0
    @1
    df-pss
    #
    wph
    @11
    @6
    wph
    @11
    wa
    #
    @4
    @5
    @11
    wph
    @2
    @4
    @12
    wph
    @2
    wa
    #
    @0
    @3
    @14
    @0
    @1
    @3
    wph
    @2
    simpr
    wph
    @1
    @3
    wss
    #
    @2
    wph
    cF
    cH
    cK
    @3
    cW
    @3
    eqid
    #
    lkrpss.f
    lkrpss.k
    wph
    cW
    clvec
    wcel
    #
    cW
    clmod
    wcel
    lkrpss.w
    cW
    lveclmod
    syl
    #
    lkrpss.h
    lkrssv
    #
    adantr
    psssstrd
    pssned
    sylan2br
    @13
    @1
    cW
    clsh
    cfv
    #
    wcel
    #
    wn
    #
    @5
    wph
    @9
    @10
    @22
    wph
    @9
    wa
    #
    @21
    @0
    @1
    @23
    @21
    @0
    @1
    wceq
    #
    @23
    @21
    wa
    #
    @9
    @24
    wph
    @9
    @21
    simplr
    @25
    @0
    @1
    @20
    cW
    @20
    eqid
    #
    wph
    @17
    @9
    @21
    lkrpss.w
    ad2antrr
    @25
    @0
    @20
    wcel
    #
    @27
    @0
    @3
    wceq
    #
    @25
    @27
    simpr
    @25
    @28
    wa
    #
    @21
    @27
    @23
    @21
    @28
    simplr
    @29
    @22
    @5
    @29
    @1
    @3
    wph
    @15
    @9
    @21
    @28
    @19
    ad3antrrr
    @29
    @3
    @0
    @1
    @25
    @28
    simpr
    wph
    @9
    @21
    @28
    simpllr
    eqsstr3d
    eqssd
    @29
    @21
    @1
    @3
    wph
    @1
    @3
    wne
    @21
    wb
    @9
    @21
    @28
    wph
    cF
    cH
    @20
    cK
    @3
    cW
    @16
    @26
    lkrpss.f
    lkrpss.k
    lkrpss.w
    lkrpss.h
    lkrshp4
    #
    ad3antrrr
    necon1bbid
    mpbird
    pm2.21dd
    wph
    @27
    @28
    wo
    @9
    @21
    wph
    cF
    cG
    @20
    cK
    @3
    cW
    @16
    @26
    lkrpss.f
    lkrpss.k
    lkrpss.w
    lkrpss.g
    lkrshpor
    ad2antrr
    mpjaodan
    @23
    @21
    simpr
    lshpcmp
    mpbid
    ex
    necon3ad
    impr
    wph
    @22
    @5
    wb
    @11
    wph
    @21
    @1
    @3
    @30
    necon1bbid
    adantr
    mpbid
    jca
    wph
    @6
    wa
    #
    @9
    @10
    @31
    @0
    @3
    @1
    wph
    @0
    @3
    wss
    @6
    wph
    cF
    cG
    cK
    @3
    cW
    @16
    lkrpss.f
    lkrpss.k
    @18
    lkrpss.g
    lkrssv
    adantr
    @31
    @1
    @3
    wph
    @4
    @5
    simprr
    eqcomd
    #
    sseqtrd
    @31
    @0
    @3
    @1
    wph
    @4
    @5
    simprl
    @32
    neeqtrd
    jca
    impbida
    syl5bb
    wph
    @4
    @7
    @5
    @8
    wph
    @0
    @3
    cG
    c.0
    wph
    cD
    cF
    cG
    cK
    @3
    cW
    c.0
    @16
    lkrpss.f
    lkrpss.k
    lkrpss.d
    lkrpss.o
    @18
    lkrpss.g
    lkr0f2
    necon3bid
    wph
    cD
    cF
    cH
    cK
    @3
    cW
    c.0
    @16
    lkrpss.f
    lkrpss.k
    lkrpss.d
    lkrpss.o
    @18
    lkrpss.h
    lkr0f2
    anbi12d
    bitrd
end
