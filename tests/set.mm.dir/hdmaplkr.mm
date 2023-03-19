include "cfv.mm"
include "csn.mm"
include "wss.mm"
include "c0g.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "sneq.mm"
include "sseq12d.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "clfn.mm"
include "crab.mm"
include "wcel.mm"
include "clcd.mm"
include "clspn.mm"
include "clmod.mm"
include "cbs.mm"
include "eqid.mm"
include "lcdlmod.mm"
include "hdmapcl.mm"
include "lspsnid.mm"
include "syl2anc.mm"
include "cmpd.mm"
include "hdmap10.mm"
include "mapdsn.mm"
include "eqtr3d.mm"
include "eleqtrd.mm"
include "wb.mm"
include "lcdvbaselfl.mm"
include "sseq2d.mm"
include "elrab3.mm"
include "syl.mm"
include "mpbid.mm"
include "adantr.mm"
include "clsh.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "chlt.mm"
include "cdif.mm"
include "anim1i.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "dochsnshp.mm"
include "csca.mm"
include "cxp.mm"
include "lcd0v.mm"
include "eqeq2d.mm"
include "hdmapeq0.mm"
include "bitr3d.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "lkrshp.mm"
include "syl3anc.mm"
include "lshpcmp.mm"
include "eqimss2.mm"
include "dvhlmod.mm"
include "lmod0vcl.mm"
include "lkrssv.mm"
include "doch0.mm"
include "sseqtr4d.mm"
include "pm2.61ne.mm"
include "eqssd.mm"

theorem hdmaplkr
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cF: class F
  let cH: class H
  let cK: class K
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vf: setvar f
  assume hdmaplkr.h: |- H = ( LHyp ` K )
  assume hdmaplkr.o: |- O = ( ( ocH ` K ) ` W )
  assume hdmaplkr.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmaplkr.v: |- V = ( Base ` U )
  assume hdmaplkr.f: |- F = ( LFnl ` U )
  assume hdmaplkr.y: |- Y = ( LKer ` U )
  assume hdmaplkr.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmaplkr.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmaplkr.x: |- ( ph -> X e. V )


  assert |- ( ph -> ( Y ` ( S ` X ) ) = ( O ` { X } ) )

  proof
    wph
    cX
    cS
    cfv
    #
    cY
    cfv
    #
    cX
    csn
    #
    cO
    cfv
    #
    wph
    @1
    @3
    wss
    #
    cU
    c0g
    cfv
    #
    cS
    cfv
    #
    cY
    cfv
    #
    @5
    csn
    #
    cO
    cfv
    #
    wss
    cX
    @5
    cX
    @5
    wceq
    #
    @1
    @7
    @3
    @9
    @10
    @0
    @6
    cY
    cX
    @5
    cS
    fveq2
    fveq2d
    @10
    @2
    @8
    cO
    cX
    @5
    sneq
    fveq2d
    sseq12d
    wph
    cX
    @5
    wne
    #
    wa
    #
    @3
    @1
    wceq
    #
    @4
    @12
    @3
    @1
    wss
    #
    @13
    wph
    @14
    @11
    wph
    @0
    @3
    vf
    cv
    #
    cY
    cfv
    #
    wss
    #
    vf
    cU
    clfn
    cfv
    #
    crab
    #
    wcel
    #
    @14
    wph
    @0
    @0
    csn
    cW
    cK
    clcd
    cfv
    cfv
    #
    clspn
    cfv
    #
    cfv
    #
    @19
    wph
    @21
    clmod
    wcel
    @0
    @21
    cbs
    cfv
    #
    wcel
    @0
    @23
    wcel
    wph
    @21
    cH
    cK
    cW
    hdmaplkr.h
    @21
    eqid
    #
    hdmaplkr.k
    lcdlmod
    wph
    @21
    @24
    cS
    cX
    cU
    cH
    cK
    cV
    cW
    hdmaplkr.h
    hdmaplkr.u
    hdmaplkr.v
    @25
    @24
    eqid
    #
    hdmaplkr.s
    hdmaplkr.k
    hdmaplkr.x
    hdmapcl
    #
    @22
    @24
    @21
    @0
    @26
    @22
    eqid
    #
    lspsnid
    syl2anc
    wph
    @2
    cU
    clspn
    cfv
    #
    cfv
    cW
    cK
    cmpd
    cfv
    cfv
    #
    cfv
    @23
    @19
    wph
    @21
    cS
    cX
    cU
    cH
    cK
    @22
    @30
    @29
    cV
    cW
    hdmaplkr.h
    hdmaplkr.u
    hdmaplkr.v
    @29
    eqid
    #
    @25
    @28
    @30
    eqid
    #
    hdmaplkr.s
    hdmaplkr.k
    hdmaplkr.x
    hdmap10
    wph
    cU
    vf
    @18
    cH
    cK
    cY
    @30
    @29
    cO
    cV
    cW
    cX
    hdmaplkr.h
    hdmaplkr.o
    @32
    hdmaplkr.u
    hdmaplkr.v
    @31
    @18
    eqid
    #
    hdmaplkr.y
    hdmaplkr.k
    hdmaplkr.x
    mapdsn
    eqtr3d
    eleqtrd
    wph
    @0
    @18
    wcel
    #
    @20
    @14
    wb
    wph
    @21
    cU
    @18
    cH
    cK
    @24
    cW
    @0
    hdmaplkr.h
    @25
    @26
    hdmaplkr.u
    @33
    hdmaplkr.k
    @27
    lcdvbaselfl
    #
    @17
    @14
    vf
    @0
    @18
    @15
    @0
    wceq
    @16
    @1
    @3
    @15
    @0
    cY
    fveq2
    sseq2d
    elrab3
    syl
    mpbid
    #
    adantr
    @12
    @3
    @1
    cU
    clsh
    cfv
    #
    cU
    @37
    eqid
    #
    wph
    cU
    clvec
    wcel
    #
    @11
    wph
    cU
    cH
    cK
    cW
    hdmaplkr.h
    hdmaplkr.u
    hdmaplkr.k
    dvhlvec
    adantr
    #
    @12
    cU
    cH
    cK
    cO
    cV
    cW
    cX
    @37
    @5
    hdmaplkr.h
    hdmaplkr.o
    hdmaplkr.u
    hdmaplkr.v
    @5
    eqid
    #
    @38
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @11
    hdmaplkr.k
    adantr
    @12
    cX
    cV
    wcel
    #
    @11
    wa
    cX
    cV
    @8
    cdif
    wcel
    wph
    @43
    @11
    hdmaplkr.x
    anim1i
    cX
    cV
    @5
    eldifsn
    sylibr
    dochsnshp
    @12
    @39
    @34
    @0
    cV
    cU
    csca
    cfv
    #
    c0g
    cfv
    #
    csn
    cxp
    #
    wne
    #
    @1
    @37
    wcel
    @40
    wph
    @34
    @11
    @35
    adantr
    wph
    @47
    @11
    wph
    @0
    @46
    cX
    @5
    wph
    @0
    @21
    c0g
    cfv
    #
    wceq
    @0
    @46
    wceq
    @10
    wph
    @48
    @46
    @0
    wph
    @21
    @44
    cU
    cH
    cK
    @48
    cV
    cW
    @45
    hdmaplkr.h
    hdmaplkr.u
    hdmaplkr.v
    @44
    eqid
    #
    @45
    eqid
    #
    @25
    @48
    eqid
    #
    hdmaplkr.k
    lcd0v
    eqeq2d
    wph
    @21
    @48
    cS
    cX
    cU
    cH
    cK
    cV
    cW
    @5
    hdmaplkr.h
    hdmaplkr.u
    hdmaplkr.v
    @41
    @25
    @51
    hdmaplkr.s
    hdmaplkr.k
    hdmaplkr.x
    hdmapeq0
    bitr3d
    necon3bid
    biimpar
    @44
    @18
    @0
    @37
    cY
    cV
    cU
    @45
    hdmaplkr.v
    @49
    @50
    @38
    @33
    hdmaplkr.y
    lkrshp
    syl3anc
    lshpcmp
    mpbid
    @1
    @3
    eqimss2
    syl
    wph
    @7
    cV
    @9
    wph
    @18
    @6
    cY
    cV
    cU
    hdmaplkr.v
    @33
    hdmaplkr.y
    wph
    cU
    cH
    cK
    cW
    hdmaplkr.h
    hdmaplkr.u
    hdmaplkr.k
    dvhlmod
    #
    wph
    @21
    cU
    @18
    cH
    cK
    @24
    cW
    @6
    hdmaplkr.h
    @25
    @26
    hdmaplkr.u
    @33
    hdmaplkr.k
    wph
    @21
    @24
    cS
    @5
    cU
    cH
    cK
    cV
    cW
    hdmaplkr.h
    hdmaplkr.u
    hdmaplkr.v
    @25
    @26
    hdmaplkr.s
    hdmaplkr.k
    wph
    cU
    clmod
    wcel
    @5
    cV
    wcel
    @52
    cV
    cU
    @5
    hdmaplkr.v
    @41
    lmod0vcl
    syl
    hdmapcl
    lcdvbaselfl
    lkrssv
    wph
    @42
    @9
    cV
    wceq
    hdmaplkr.k
    cU
    cH
    cK
    cO
    cV
    cW
    @5
    hdmaplkr.h
    hdmaplkr.u
    hdmaplkr.o
    hdmaplkr.v
    @41
    doch0
    syl
    sseqtr4d
    pm2.61ne
    @36
    eqssd
end
