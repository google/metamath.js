include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "cico.mm"
include "co.mm"
include "cixp.mm"
include "wcel.mm"
include "crrx.mm"
include "cds.mm"
include "cbl.mm"
include "wss.mm"
include "wa.mm"
include "cq.mm"
include "cmap.mm"
include "wrex.mm"
include "csn.mm"
include "0ex.mm"
include "snid.mm"
include "a1i.mm"
include "cr.mm"
include "adantr.mm"
include "oveq2.mm"
include "cvv.mm"
include "reex.mm"
include "mapdm0.mm"
include "ax-mp.mm"
include "eqtrd.mm"
include "adantl.mm"
include "eleqtrd.mm"
include "cxmt.mm"
include "crp.mm"
include "cme.mm"
include "cfn.mm"
include "0fin.mm"
include "eqid.mm"
include "rrxmetfi.mm"
include "metxmet.mm"
include "syl6eleqr.mm"
include "blcntr.mm"
include "syl3anc.mm"
include "elsni.mm"
include "syl.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "snssd.mm"
include "jca.mm"
include "biidd.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wb.mm"
include "qex.mm"
include "eqtr2d.mm"
include "eleq2d.mm"
include "anbi1d.mm"
include "rexbidv2.mm"
include "anbi12d.mm"
include "mpbird.mm"
include "ixpeq1.mm"
include "ixp0x.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveqd.mm"
include "sseq12d.mm"
include "rexbidv.mm"
include "wn.mm"
include "wne.mm"
include "neqne.mm"
include "hoiqssbllem3.mm"
include "pm2.61dan.mm"

theorem hoiqssbl
  let wph: wff ph
  let vi: setvar i
  let cE: class E
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vd: setvar d
  let vk: setvar k
  let vx: setvar x
  assume hoiqssbl.x: |- ( ph -> X e. Fin )
  assume hoiqssbl.y: |- ( ph -> Y e. ( RR ^m X ) )
  assume hoiqssbl.e: |- ( ph -> E e. RR+ )

  disjoint E c
  disjoint E d
  disjoint E i
  disjoint c d
  disjoint c i
  disjoint d i
  disjoint X c
  disjoint X d
  disjoint X i
  disjoint Y c
  disjoint Y d
  disjoint Y i
  disjoint c ph
  disjoint d ph
  disjoint i ph
  disjoint k x
  assert |- ( ph -> E. c e. ( QQ ^m X ) E. d e. ( QQ ^m X ) ( Y e. X_ i e. X ( ( c ` i ) [,) ( d ` i ) ) /\ X_ i e. X ( ( c ` i ) [,) ( d ` i ) ) C_ ( Y ( ball ` ( dist ` ( RR^ ` X ) ) ) E ) ) )

  proof
    wph
    cX
    c0
    wceq
    #
    cY
    vi
    cX
    vi
    cv
    #
    vc
    cv
    #
    cfv
    @1
    vd
    cv
    #
    cfv
    cico
    co
    #
    cixp
    #
    wcel
    #
    @5
    cY
    cE
    cX
    crrx
    cfv
    #
    cds
    cfv
    #
    cbl
    cfv
    #
    co
    #
    wss
    #
    wa
    #
    vd
    cq
    cX
    cmap
    co
    #
    wrex
    #
    vc
    @13
    wrex
    #
    wph
    @0
    wa
    #
    @15
    cY
    c0
    csn
    #
    wcel
    #
    @17
    cY
    cE
    c0
    crrx
    cfv
    #
    cds
    cfv
    #
    cbl
    cfv
    #
    co
    #
    wss
    #
    wa
    #
    vd
    @13
    wrex
    #
    vc
    @13
    wrex
    #
    @16
    @26
    @24
    vd
    @17
    wrex
    #
    vc
    @17
    wrex
    #
    @16
    c0
    @17
    wcel
    #
    @27
    @28
    @29
    @16
    c0
    0ex
    snid
    a1i
    #
    @16
    @29
    @24
    @27
    @30
    @16
    @18
    @23
    @16
    cY
    cr
    cX
    cmap
    co
    #
    @17
    wph
    cY
    @31
    wcel
    #
    @0
    hoiqssbl.y
    adantr
    @0
    @31
    @17
    wceq
    wph
    @0
    @31
    cr
    c0
    cmap
    co
    #
    @17
    cX
    c0
    cr
    cmap
    oveq2
    @33
    @17
    wceq
    #
    @0
    cr
    cvv
    wcel
    @34
    reex
    cr
    cvv
    mapdm0
    ax-mp
    #
    a1i
    eqtrd
    adantl
    eleqtrd
    #
    @16
    c0
    @22
    @16
    c0
    c0
    cE
    @21
    co
    #
    @22
    @16
    @20
    @33
    cxmt
    cfv
    wcel
    #
    c0
    @33
    wcel
    cE
    crp
    wcel
    #
    c0
    @37
    wcel
    @38
    @16
    @20
    @33
    cme
    cfv
    wcel
    #
    @38
    c0
    cfn
    wcel
    @40
    0fin
    @20
    c0
    @20
    eqid
    rrxmetfi
    ax-mp
    @20
    @33
    metxmet
    ax-mp
    a1i
    @16
    c0
    @17
    @33
    @30
    @35
    syl6eleqr
    wph
    @39
    @0
    hoiqssbl.e
    adantr
    @20
    c0
    cE
    @33
    blcntr
    syl3anc
    @16
    c0
    cY
    cE
    @21
    @16
    cY
    c0
    @16
    @18
    cY
    c0
    wceq
    @36
    cY
    c0
    elsni
    syl
    eqcomd
    oveq1d
    eleqtrd
    snssd
    jca
    @24
    @24
    vd
    c0
    @17
    @3
    c0
    wceq
    @24
    biidd
    rspcev
    syl2anc
    @27
    @27
    vc
    c0
    @17
    @2
    c0
    wceq
    @27
    biidd
    rspcev
    syl2anc
    @0
    @26
    @28
    wb
    wph
    @0
    @25
    @27
    vc
    @13
    @17
    @0
    @2
    @13
    wcel
    @2
    @17
    wcel
    @25
    @27
    @0
    @13
    @17
    @2
    @0
    @17
    @13
    @0
    @13
    cq
    c0
    cmap
    co
    #
    @17
    cX
    c0
    cq
    cmap
    oveq2
    @41
    @17
    wceq
    #
    @0
    cq
    cvv
    wcel
    @42
    qex
    cq
    cvv
    mapdm0
    ax-mp
    a1i
    eqtr2d
    eqcomd
    #
    eleq2d
    @0
    @24
    @24
    vd
    @13
    @17
    @0
    @3
    @13
    wcel
    @3
    @17
    wcel
    @24
    @0
    @13
    @17
    @3
    @43
    eleq2d
    anbi1d
    rexbidv2
    anbi12d
    rexbidv2
    adantl
    mpbird
    @0
    @15
    @26
    wb
    wph
    @0
    @14
    @25
    vc
    @13
    @0
    @12
    @24
    vd
    @13
    @0
    @6
    @18
    @11
    @23
    @0
    @5
    @17
    cY
    @0
    @5
    vi
    c0
    @4
    cixp
    #
    @17
    vi
    cX
    c0
    @4
    ixpeq1
    @44
    @17
    wceq
    @0
    vi
    @4
    ixp0x
    a1i
    eqtrd
    #
    eleq2d
    @0
    @5
    @17
    @10
    @22
    @45
    @0
    @9
    @21
    cY
    cE
    @0
    @8
    @20
    cbl
    @0
    @7
    @19
    cds
    cX
    c0
    crrx
    fveq2
    fveq2d
    fveq2d
    oveqd
    sseq12d
    anbi12d
    rexbidv
    rexbidv
    adantl
    mpbird
    wph
    @0
    wn
    #
    wa
    vi
    cE
    cX
    cY
    vc
    vd
    wph
    cX
    cfn
    wcel
    @46
    hoiqssbl.x
    adantr
    @46
    cX
    c0
    wne
    wph
    cX
    c0
    neqne
    adantl
    wph
    @32
    @46
    hoiqssbl.y
    adantr
    wph
    @39
    @46
    hoiqssbl.e
    adantr
    hoiqssbllem3
    pm2.61dan
end
