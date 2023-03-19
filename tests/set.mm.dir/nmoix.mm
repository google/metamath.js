include "cngp.mm"
include "wcel.mm"
include "cghm.mm"
include "co.mm"
include "w3a.mm"
include "wa.mm"
include "cfv.mm"
include "cr.mm"
include "cxmu.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmul.mm"
include "cnghm.mm"
include "isnghm2.mm"
include "biimpar.mm"
include "nmoi.mm"
include "sylan.mm"
include "an32s.mm"
include "id.mm"
include "nmcl.mm"
include "3ad2antl1.mm"
include "rexmul.mm"
include "syl2anr.mm"
include "breqtrrd.mm"
include "c0g.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "wne.mm"
include "cxr.mm"
include "cbs.mm"
include "simpl2.mm"
include "eqid.mm"
include "ghmf.mm"
include "ffvelrnda.mm"
include "3ad2antl3.mm"
include "syl2anc.mm"
include "adantr.mm"
include "rexrd.mm"
include "pnfge.mm"
include "syl.mm"
include "crp.mm"
include "simp1.mm"
include "nmrpcl.mm"
include "3expa.mm"
include "sylanl1.mm"
include "cc0.mm"
include "clt.mm"
include "rpxr.mm"
include "rpgt0.mm"
include "xmulpnf2.mm"
include "0le0.mm"
include "simpl3.mm"
include "ghmid.mm"
include "nm0.mm"
include "eqtrd.mm"
include "simpl1.mm"
include "pnfxr.mm"
include "xmul01.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "mpbiri.mm"
include "pm2.61ne.mm"
include "simpr.mm"
include "oveq1d.mm"
include "wo.mm"
include "cmnf.mm"
include "nmocl.mm"
include "nmoge0.mm"
include "ge0nemnf.mm"
include "jca.mm"
include "xrnemnf.mm"
include "sylib.mm"
include "mpjaodan.mm"

theorem nmoix
  let cS: class S
  let cT: class T
  let cF: class F
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let cX: class X
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let cA: class A
  let wph: wff ph
  assume nmofval.1: |- N = ( S normOp T )
  assume nmoi.2: |- V = ( Base ` S )
  assume nmoi.3: |- L = ( norm ` S )
  assume nmoi.4: |- M = ( norm ` T )


  assert |- ( ( ( S e. NrmGrp /\ T e. NrmGrp /\ F e. ( S GrpHom T ) ) /\ X e. V ) -> ( M ` ( F ` X ) ) <_ ( ( N ` F ) *e ( L ` X ) ) )

  proof
    cS
    cngp
    wcel
    #
    cT
    cngp
    wcel
    #
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    w3a
    #
    cX
    cV
    wcel
    #
    wa
    #
    cF
    cN
    cfv
    #
    cr
    wcel
    #
    cX
    cF
    cfv
    #
    cM
    cfv
    #
    @6
    cX
    cL
    cfv
    #
    cxmu
    co
    #
    cle
    wbr
    @6
    cpnf
    wceq
    #
    @5
    @7
    wa
    @9
    @6
    @10
    cmul
    co
    #
    @11
    cle
    @3
    @7
    @4
    @9
    @13
    cle
    wbr
    #
    @3
    @7
    wa
    cF
    cS
    cT
    cnghm
    co
    wcel
    #
    @4
    @14
    @3
    @15
    @7
    cS
    cT
    cF
    cN
    nmofval.1
    isnghm2
    biimpar
    cS
    cT
    cF
    cL
    cM
    cN
    cV
    cX
    nmofval.1
    nmoi.2
    nmoi.3
    nmoi.4
    nmoi
    sylan
    an32s
    @7
    @7
    @10
    cr
    wcel
    #
    @11
    @13
    wceq
    @5
    @7
    id
    @0
    @1
    @4
    @16
    @2
    cX
    cS
    cL
    cV
    nmoi.2
    nmoi.3
    nmcl
    3ad2antl1
    @6
    @10
    rexmul
    syl2anr
    breqtrrd
    @5
    @12
    wa
    #
    @9
    cpnf
    @10
    cxmu
    co
    #
    @11
    cle
    @5
    @9
    @18
    cle
    wbr
    #
    @12
    @5
    @19
    cS
    c0g
    cfv
    #
    cF
    cfv
    #
    cM
    cfv
    #
    cpnf
    @20
    cL
    cfv
    #
    cxmu
    co
    #
    cle
    wbr
    #
    cX
    @20
    cX
    @20
    wceq
    #
    @9
    @22
    @18
    @24
    cle
    @26
    @8
    @21
    cM
    cX
    @20
    cF
    fveq2
    fveq2d
    @26
    @10
    @23
    cpnf
    cxmu
    cX
    @20
    cL
    fveq2
    oveq2d
    breq12d
    @5
    cX
    @20
    wne
    #
    wa
    #
    @9
    cpnf
    @18
    cle
    @28
    @9
    cxr
    wcel
    @9
    cpnf
    cle
    wbr
    @28
    @9
    @5
    @9
    cr
    wcel
    #
    @27
    @5
    @1
    @8
    cT
    cbs
    cfv
    #
    wcel
    #
    @29
    @0
    @1
    @2
    @4
    simpl2
    #
    @2
    @0
    @4
    @31
    @1
    @2
    cV
    @30
    cX
    cF
    cS
    cT
    cF
    cV
    @30
    nmoi.2
    @30
    eqid
    #
    ghmf
    ffvelrnda
    3ad2antl3
    @8
    cT
    cM
    @30
    @33
    nmoi.4
    nmcl
    syl2anc
    adantr
    rexrd
    @9
    pnfge
    syl
    @28
    @10
    crp
    wcel
    #
    @18
    cpnf
    wceq
    #
    @3
    @0
    @4
    @27
    @34
    @0
    @1
    @2
    simp1
    @0
    @4
    @27
    @34
    cX
    cS
    cL
    cV
    @20
    nmoi.2
    nmoi.3
    @20
    eqid
    #
    nmrpcl
    3expa
    sylanl1
    @34
    @10
    cxr
    wcel
    cc0
    @10
    clt
    wbr
    @35
    @10
    rpxr
    @10
    rpgt0
    @10
    xmulpnf2
    syl2anc
    syl
    breqtrrd
    @5
    @25
    cc0
    cc0
    cle
    wbr
    0le0
    @5
    @22
    cc0
    @24
    cc0
    cle
    @5
    @22
    cT
    c0g
    cfv
    #
    cM
    cfv
    #
    cc0
    @5
    @21
    @37
    cM
    @5
    @2
    @21
    @37
    wceq
    @0
    @1
    @2
    @4
    simpl3
    cS
    cT
    cF
    @20
    @37
    @36
    @37
    eqid
    #
    ghmid
    syl
    fveq2d
    @5
    @1
    @38
    cc0
    wceq
    @32
    cT
    cM
    @37
    nmoi.4
    @39
    nm0
    syl
    eqtrd
    @5
    @24
    cpnf
    cc0
    cxmu
    co
    #
    cc0
    @5
    @23
    cc0
    cpnf
    cxmu
    @5
    @0
    @23
    cc0
    wceq
    @0
    @1
    @2
    @4
    simpl1
    cS
    cL
    @20
    nmoi.3
    @36
    nm0
    syl
    oveq2d
    cpnf
    cxr
    wcel
    @40
    cc0
    wceq
    pnfxr
    cpnf
    xmul01
    ax-mp
    syl6eq
    breq12d
    mpbiri
    pm2.61ne
    adantr
    @17
    @6
    cpnf
    @10
    cxmu
    @5
    @12
    simpr
    oveq1d
    breqtrrd
    @3
    @7
    @12
    wo
    #
    @4
    @3
    @6
    cxr
    wcel
    #
    @6
    cmnf
    wne
    #
    wa
    @41
    @3
    @42
    @43
    cS
    cT
    cF
    cN
    nmofval.1
    nmocl
    #
    @3
    @42
    cc0
    @6
    cle
    wbr
    @43
    @44
    cS
    cT
    cF
    cN
    nmofval.1
    nmoge0
    @6
    ge0nemnf
    syl2anc
    jca
    @6
    xrnemnf
    sylib
    adantr
    mpjaodan
end
