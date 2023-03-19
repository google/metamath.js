include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "co.mm"
include "cxad.mm"
include "cle.mm"
include "cxne.mm"
include "wbr.mm"
include "cbl.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cr.mm"
include "cpnf.mm"
include "cmin.mm"
include "simprr.mm"
include "simprl.mm"
include "rexsub.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "simpll.mm"
include "adantr.mm"
include "resubcld.mm"
include "leidd.mm"
include "xmetsym.mm"
include "syl3anc.mm"
include "eqcomd.mm"
include "recnd.mm"
include "nncand.mm"
include "3brtr4d.mm"
include "blss2.mm"
include "syl33anc.mm"
include "eqsstrd.mm"
include "expr.mm"
include "cxr.mm"
include "cc0.mm"
include "cicc.mm"
include "wf.mm"
include "metdsf.mm"
include "ffvelrnd.mm"
include "elxrge0.mm"
include "simplbi.mm"
include "syl.mm"
include "xmetcl.mm"
include "xnegcld.mm"
include "xaddcld.mm"
include "adantrr.mm"
include "pnfxr.mm"
include "a1i.mm"
include "pnfge.mm"
include "ssbl.mm"
include "syl221anc.mm"
include "wb.mm"
include "xblpnf.mm"
include "mpbir2and.mm"
include "blpnfctr.mm"
include "eqtr2d.mm"
include "sseqtrd.mm"
include "cmnf.mm"
include "wne.mm"
include "wo.mm"
include "simprbi.mm"
include "ge0nemnf.mm"
include "jca.mm"
include "xrnemnf.mm"
include "sylib.mm"
include "mpjaod.mm"
include "clt.mm"
include "wn.mm"
include "pnfnlt.mm"
include "xbln0.mm"
include "xposdif.mm"
include "bitr4d.mm"
include "breq1.mm"
include "sylan9bb.mm"
include "necon1bbid.mm"
include "mpbid.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "xmetge0.mm"
include "mpjaodan.mm"
include "sslin.mm"
include "xrleid.mm"
include "simplr.mm"
include "metdsge.mm"
include "syl31anc.mm"
include "sseq0.mm"
include "mpbird.mm"
include "xlesubadd.mm"
include "xaddcom.mm"
include "breqtrd.mm"

theorem metdstri
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cS: class S
  let cF: class F
  let cX: class X
  let vr: setvar r
  let vw: setvar w
  let vz: setvar z
  let vs: setvar s
  let vt: setvar t
  let cJ: class J
  let wph: wff ph
  let cC: class C
  let cG: class G
  let cR: class R
  let cT: class T
  let cK: class K
  let cU: class U
  let cV: class V
  assume metdscn.f: |- F = ( x e. X |-> inf ( ran ( y e. S |-> ( x D y ) ) , RR* , < ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint D x
  disjoint D y
  disjoint B x
  disjoint B y
  disjoint S x
  disjoint S y
  disjoint X x
  disjoint X y
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint r s
  disjoint r t
  disjoint D r
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint D s
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint D t
  disjoint D w
  disjoint D z
  disjoint J r
  disjoint J s
  disjoint J t
  disjoint J w
  disjoint J y
  disjoint J z
  disjoint ph s
  disjoint ph t
  disjoint C r
  disjoint C s
  disjoint C w
  disjoint C z
  disjoint G s
  disjoint G t
  disjoint R w
  disjoint R z
  disjoint T s
  disjoint T t
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint K r
  disjoint K s
  disjoint K w
  disjoint K z
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint S w
  disjoint S z
  disjoint U s
  disjoint U w
  disjoint X r
  disjoint X s
  disjoint X t
  disjoint X w
  disjoint X z
  disjoint F r
  disjoint F s
  disjoint F t
  disjoint F w
  disjoint F z
  disjoint V w
  disjoint V z
  assert |- ( ( ( D e. ( *Met ` X ) /\ S C_ X ) /\ ( A e. X /\ B e. X ) ) -> ( F ` A ) <_ ( ( A D B ) +e ( F ` B ) ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    wa
    #
    wa
    #
    cA
    cF
    cfv
    #
    cB
    cF
    cfv
    #
    cA
    cB
    cD
    co
    #
    cxad
    co
    #
    @9
    @8
    cxad
    co
    #
    cle
    @6
    @7
    @9
    cxne
    #
    cxad
    co
    #
    @8
    cle
    wbr
    #
    @7
    @10
    cle
    wbr
    #
    @6
    @14
    cS
    cB
    @13
    cD
    cbl
    cfv
    #
    co
    #
    cin
    #
    c0
    wceq
    #
    @6
    @18
    cS
    cA
    @7
    @16
    co
    #
    cin
    #
    wss
    #
    @21
    c0
    wceq
    #
    @19
    @6
    @17
    @20
    wss
    #
    @22
    @6
    @9
    cr
    wcel
    #
    @24
    @9
    cpnf
    wceq
    #
    @6
    @25
    wa
    #
    @7
    cr
    wcel
    #
    @24
    @7
    cpnf
    wceq
    #
    @6
    @25
    @28
    @24
    @6
    @25
    @28
    wa
    #
    wa
    #
    @17
    cB
    @7
    @9
    cmin
    co
    #
    @16
    co
    #
    @20
    @31
    @13
    @32
    cB
    @16
    @31
    @28
    @25
    @13
    @32
    wceq
    @6
    @25
    @28
    simprr
    #
    @6
    @25
    @28
    simprl
    #
    @7
    @9
    rexsub
    syl2anc
    oveq2d
    @31
    @0
    @4
    @3
    @32
    cr
    wcel
    @28
    cB
    cA
    cD
    co
    #
    @7
    @32
    cmin
    co
    #
    cle
    wbr
    @33
    @20
    wss
    @6
    @0
    @30
    @0
    @1
    @5
    simpll
    #
    adantr
    @6
    @4
    @30
    @2
    @3
    @4
    simprr
    #
    adantr
    @6
    @3
    @30
    @2
    @3
    @4
    simprl
    #
    adantr
    @31
    @7
    @9
    @34
    @35
    resubcld
    @34
    @31
    @9
    @9
    @36
    @37
    cle
    @31
    @9
    @35
    leidd
    @31
    @9
    @36
    @6
    @9
    @36
    wceq
    #
    @30
    @6
    @0
    @3
    @4
    @41
    @38
    @40
    @39
    cA
    cB
    cD
    cX
    xmetsym
    syl3anc
    adantr
    eqcomd
    @31
    @7
    @9
    @31
    @7
    @34
    recnd
    @31
    @9
    @35
    recnd
    nncand
    3brtr4d
    cD
    cB
    cA
    @32
    @7
    cX
    blss2
    syl33anc
    eqsstrd
    expr
    @6
    @25
    @29
    @24
    @6
    @25
    @29
    wa
    #
    wa
    #
    @17
    cB
    cpnf
    @16
    co
    #
    @20
    @43
    @0
    @4
    @13
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    @13
    cpnf
    cle
    wbr
    #
    @17
    @44
    wss
    @6
    @0
    @42
    @38
    adantr
    #
    @6
    @4
    @42
    @39
    adantr
    #
    @6
    @25
    @45
    @29
    @27
    @7
    @12
    @6
    @7
    cxr
    wcel
    #
    @25
    @6
    @7
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @50
    @6
    cX
    @51
    cA
    cF
    @2
    cX
    @51
    cF
    wf
    @5
    vx
    vy
    cD
    cS
    cF
    cX
    metdscn.f
    metdsf
    adantr
    #
    @40
    ffvelrnd
    #
    @52
    @50
    cc0
    @7
    cle
    wbr
    #
    @7
    elxrge0
    #
    simplbi
    syl
    #
    adantr
    @27
    @9
    @6
    @9
    cxr
    wcel
    #
    @25
    @6
    @0
    @3
    @4
    @58
    @38
    @40
    @39
    cA
    cB
    cD
    cX
    xmetcl
    syl3anc
    #
    adantr
    xnegcld
    xaddcld
    adantrr
    #
    @46
    @43
    pnfxr
    a1i
    @43
    @45
    @47
    @60
    @13
    pnfge
    syl
    cD
    cB
    @13
    cpnf
    cX
    ssbl
    syl221anc
    @43
    @20
    cA
    cpnf
    @16
    co
    #
    @44
    @43
    @7
    cpnf
    cA
    @16
    @6
    @25
    @29
    simprr
    oveq2d
    @43
    @0
    @3
    cB
    @61
    wcel
    #
    @61
    @44
    wceq
    @48
    @6
    @3
    @42
    @40
    adantr
    #
    @43
    @62
    @4
    @25
    @49
    @6
    @25
    @29
    simprl
    @43
    @0
    @3
    @62
    @4
    @25
    wa
    wb
    @48
    @63
    cB
    cD
    cA
    cX
    xblpnf
    syl2anc
    mpbir2and
    cB
    cD
    cA
    cX
    blpnfctr
    syl3anc
    eqtr2d
    sseqtrd
    expr
    @27
    @50
    @7
    cmnf
    wne
    #
    wa
    #
    @28
    @29
    wo
    @6
    @65
    @25
    @6
    @50
    @64
    @57
    @6
    @50
    @55
    @64
    @57
    @6
    @52
    @55
    @54
    @52
    @50
    @55
    @56
    simprbi
    syl
    #
    @7
    ge0nemnf
    syl2anc
    jca
    adantr
    @7
    xrnemnf
    sylib
    mpjaod
    @6
    @26
    wa
    #
    @17
    c0
    @20
    @67
    cpnf
    @7
    clt
    wbr
    #
    wn
    #
    @17
    c0
    wceq
    @6
    @69
    @26
    @6
    @50
    @69
    @57
    @7
    pnfnlt
    syl
    adantr
    @67
    @68
    @17
    c0
    @6
    @17
    c0
    wne
    #
    @9
    @7
    clt
    wbr
    #
    @26
    @68
    @6
    @70
    cc0
    @13
    clt
    wbr
    #
    @71
    @6
    @0
    @4
    @45
    @70
    @72
    wb
    @38
    @39
    @6
    @7
    @12
    @57
    @6
    @9
    @59
    xnegcld
    xaddcld
    #
    cD
    cB
    @13
    cX
    xbln0
    syl3anc
    @6
    @58
    @50
    @71
    @72
    wb
    @59
    @57
    @9
    @7
    xposdif
    syl2anc
    bitr4d
    @9
    cpnf
    @7
    clt
    breq1
    sylan9bb
    necon1bbid
    mpbid
    @20
    0ss
    syl6eqss
    @6
    @58
    @9
    cmnf
    wne
    #
    wa
    @25
    @26
    wo
    @6
    @58
    @74
    @59
    @6
    @58
    cc0
    @9
    cle
    wbr
    #
    @74
    @59
    @6
    @0
    @3
    @4
    @75
    @38
    @40
    @39
    cA
    cB
    cD
    cX
    xmetge0
    syl3anc
    @9
    ge0nemnf
    syl2anc
    #
    jca
    @9
    xrnemnf
    sylib
    mpjaodan
    @17
    @20
    cS
    sslin
    syl
    @6
    @7
    @7
    cle
    wbr
    #
    @23
    @6
    @50
    @77
    @57
    @7
    xrleid
    syl
    @6
    @0
    @1
    @3
    @50
    @77
    @23
    wb
    @38
    @0
    @1
    @5
    simplr
    #
    @40
    @57
    vx
    vy
    cA
    cD
    @7
    cS
    cF
    cX
    metdscn.f
    metdsge
    syl31anc
    mpbid
    @18
    @21
    sseq0
    syl2anc
    @6
    @0
    @1
    @4
    @45
    @14
    @19
    wb
    @38
    @78
    @39
    @73
    vx
    vy
    cB
    cD
    @13
    cS
    cF
    cX
    metdscn.f
    metdsge
    syl31anc
    mpbird
    @6
    @50
    @58
    @8
    cxr
    wcel
    #
    @55
    @74
    cc0
    @8
    cle
    wbr
    #
    @14
    @15
    wb
    @57
    @59
    @6
    @8
    @51
    wcel
    #
    @79
    @6
    cX
    @51
    cB
    cF
    @53
    @39
    ffvelrnd
    #
    @81
    @79
    @80
    @8
    elxrge0
    #
    simplbi
    syl
    #
    @66
    @76
    @6
    @81
    @80
    @82
    @81
    @79
    @80
    @83
    simprbi
    syl
    @7
    @9
    @8
    xlesubadd
    syl33anc
    mpbid
    @6
    @79
    @58
    @10
    @11
    wceq
    @84
    @59
    @8
    @9
    xaddcom
    syl2anc
    breqtrd
end
