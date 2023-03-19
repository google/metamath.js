include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cfv.mm"
include "cr.mm"
include "cv.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "cmul.mm"
include "co.mm"
include "cpnf.mm"
include "cico.mm"
include "wceq.mm"
include "simpll.mm"
include "simpr.mm"
include "cle.mm"
include "wbr.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "rpge0.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "itg2const.mm"
include "syl3anc.mm"
include "remulcld.mm"
include "eqeltrd.mm"
include "covol.mm"
include "mblvol.mm"
include "ad2antrr.mm"
include "c1.mm"
include "caddc.mm"
include "cdiv.mm"
include "wss.mm"
include "mblss.mm"
include "ad3antrrr.mm"
include "peano2re.mm"
include "adantl.mm"
include "simplr.mm"
include "rerpdivcld.mm"
include "adantr.mm"
include "ovollecl.mm"
include "wrex.mm"
include "cicc.mm"
include "simplll.mm"
include "cxr.mm"
include "rexrd.mm"
include "wf.mm"
include "elxrge0.mm"
include "0e0iccpnf.mm"
include "ifcl.mm"
include "sylancl.mm"
include "eqid.mm"
include "fmptd.mm"
include "itg2ge0.mm"
include "syl.mm"
include "ge0p1rpd.mm"
include "rpdivcld.mm"
include "rpge0d.mm"
include "breq2d.mm"
include "biimpar.mm"
include "w3a.mm"
include "wb.mm"
include "0xr.mm"
include "iccssxr.mm"
include "volf.mm"
include "ffvelrni.mm"
include "sseldi.mm"
include "elicc1.mm"
include "sylancr.mm"
include "mpbir3and.mm"
include "volivth.mm"
include "syl2anc.mm"
include "ex.mm"
include "simprl.mm"
include "simprrr.mm"
include "oveq2d.mm"
include "recnd.mm"
include "wne.mm"
include "rpne0.mm"
include "divcan2d.mm"
include "3eqtrd.mm"
include "cofr.mm"
include "simpl.mm"
include "wral.mm"
include "leidd.mm"
include "iftrue.mm"
include "sselda.mm"
include "iftrued.mm"
include "3brtr4d.mm"
include "wn.mm"
include "iffalse.mm"
include "0le0.mm"
include "breq2.mm"
include "ifboth.mm"
include "eqbrtrd.mm"
include "pm2.61dan.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "reex.mm"
include "a1i.mm"
include "eqidd.mm"
include "ofrfval2.mm"
include "syldan.mm"
include "syl2an.mm"
include "itg2le.mm"
include "eqbrtrrd.mm"
include "clt.mm"
include "ltp1.mm"
include "ltnled.mm"
include "mpbid.mm"
include "pm2.21dd.mm"
include "rexlimdvaa.mm"
include "syld.mm"
include "imp.mm"
include "wo.mm"
include "eqeltrrd.mm"
include "xrletri.mm"
include "mpjaodan.mm"
include "impbida.mm"

theorem itg2const2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vg: setvar g
  let vz: setvar z
  let vh: setvar h
  let vy: setvar y
  let cF: class F
  let cG: class G

  disjoint A x
  disjoint B x
  disjoint g x
  disjoint g z
  disjoint A g
  disjoint x z
  disjoint A z
  disjoint B z
  disjoint g h
  disjoint g y
  disjoint F g
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint F h
  disjoint x y
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G g
  disjoint G h
  disjoint G x
  disjoint G y
  disjoint G z
  assert |- ( ( A e. dom vol /\ B e. RR+ ) -> ( ( vol ` A ) e. RR <-> ( S.2 ` ( x e. RR |-> if ( x e. A , B , 0 ) ) ) e. RR ) )

  proof
    cA
    cvol
    cdm
    #
    wcel
    #
    cB
    crp
    wcel
    #
    wa
    #
    cA
    cvol
    cfv
    #
    cr
    wcel
    #
    vx
    cr
    vx
    cv
    #
    cA
    wcel
    #
    cB
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    wcel
    #
    @3
    @5
    wa
    #
    @10
    cB
    @4
    cmul
    co
    #
    cr
    @12
    @1
    @5
    cB
    cc0
    cpnf
    cico
    co
    wcel
    #
    @10
    @13
    wceq
    @1
    @2
    @5
    simpll
    @3
    @5
    simpr
    #
    @12
    cB
    cr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    @14
    @2
    @16
    @1
    @5
    cB
    rpre
    #
    ad2antlr
    #
    @2
    @17
    @1
    @5
    cB
    rpge0
    #
    ad2antlr
    cB
    elrege0
    #
    sylanbrc
    vx
    cA
    cB
    itg2const
    syl3anc
    @12
    cB
    @4
    @19
    @15
    remulcld
    eqeltrd
    @3
    @11
    wa
    #
    @4
    cA
    covol
    cfv
    #
    cr
    @1
    @4
    @23
    wceq
    @2
    @11
    cA
    mblvol
    ad2antrr
    #
    @22
    @23
    @10
    c1
    caddc
    co
    #
    cB
    cdiv
    co
    #
    cle
    wbr
    #
    @23
    cr
    wcel
    #
    @26
    @23
    cle
    wbr
    #
    @22
    @27
    wa
    cA
    cr
    wss
    #
    @26
    cr
    wcel
    #
    @27
    @28
    @1
    @30
    @2
    @11
    @27
    cA
    mblss
    ad3antrrr
    @22
    @31
    @27
    @22
    @25
    cB
    @11
    @25
    cr
    wcel
    #
    @3
    @10
    peano2re
    #
    adantl
    #
    @1
    @2
    @11
    simplr
    #
    rerpdivcld
    #
    adantr
    @22
    @27
    simpr
    cA
    @26
    ovollecl
    syl3anc
    @22
    @29
    @28
    @22
    @29
    vz
    cv
    #
    cA
    wss
    #
    @37
    cvol
    cfv
    #
    @26
    wceq
    #
    wa
    #
    vz
    @0
    wrex
    #
    @28
    @22
    @29
    @42
    @22
    @29
    wa
    #
    @1
    @26
    cc0
    @4
    cicc
    co
    wcel
    #
    @42
    @1
    @2
    @11
    @29
    simplll
    #
    @43
    @44
    @26
    cxr
    wcel
    #
    cc0
    @26
    cle
    wbr
    #
    @26
    @4
    cle
    wbr
    #
    @43
    @26
    @22
    @31
    @29
    @36
    adantr
    rexrd
    @22
    @47
    @29
    @22
    @26
    @22
    @25
    cB
    @22
    @10
    @3
    @11
    simpr
    @22
    cr
    cc0
    cpnf
    cicc
    co
    #
    @9
    wf
    #
    cc0
    @10
    cle
    wbr
    @3
    @50
    @11
    @3
    vx
    cr
    @8
    @49
    @9
    @3
    @6
    cr
    wcel
    #
    wa
    #
    cB
    @49
    wcel
    #
    cc0
    @49
    wcel
    #
    @8
    @49
    wcel
    @52
    cB
    cxr
    wcel
    #
    @17
    @53
    @52
    cB
    @2
    @16
    @1
    @51
    @18
    ad2antlr
    rexrd
    @2
    @17
    @1
    @51
    @20
    ad2antlr
    cB
    elxrge0
    #
    sylanbrc
    0e0iccpnf
    @7
    cB
    cc0
    @49
    ifcl
    sylancl
    #
    @9
    eqid
    fmptd
    adantr
    #
    @9
    itg2ge0
    syl
    ge0p1rpd
    @35
    rpdivcld
    rpge0d
    adantr
    @22
    @48
    @29
    @22
    @4
    @23
    @26
    cle
    @24
    breq2d
    biimpar
    @43
    cc0
    cxr
    wcel
    @4
    cxr
    wcel
    #
    @44
    @46
    @47
    @48
    w3a
    wb
    0xr
    @43
    @1
    @59
    @45
    @1
    @49
    cxr
    @4
    cc0
    cpnf
    iccssxr
    @0
    @49
    cA
    cvol
    volf
    ffvelrni
    sseldi
    #
    syl
    cc0
    @4
    @26
    elicc1
    sylancr
    mpbir3and
    vz
    cA
    @26
    volivth
    syl2anc
    ex
    @22
    @41
    @28
    vz
    @0
    @22
    @37
    @0
    wcel
    #
    @41
    wa
    #
    wa
    #
    @25
    @10
    cle
    wbr
    #
    @28
    @63
    vx
    cr
    @6
    @37
    wcel
    #
    cB
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    @25
    @10
    cle
    @63
    @68
    cB
    @39
    cmul
    co
    #
    cB
    @26
    cmul
    co
    #
    @25
    @63
    @61
    @39
    cr
    wcel
    @14
    @68
    @69
    wceq
    @22
    @61
    @41
    simprl
    @63
    @39
    @26
    cr
    @22
    @61
    @38
    @40
    simprrr
    #
    @22
    @31
    @62
    @36
    adantr
    eqeltrd
    @63
    @16
    @17
    @14
    @22
    @16
    @62
    @2
    @16
    @1
    @11
    @18
    ad2antlr
    #
    adantr
    @63
    cB
    @22
    @2
    @62
    @35
    adantr
    rpge0d
    @21
    sylanbrc
    vx
    @37
    cB
    itg2const
    syl3anc
    @63
    @39
    @26
    cB
    cmul
    @71
    oveq2d
    @22
    @70
    @25
    wceq
    @62
    @22
    @25
    cB
    @22
    @25
    @34
    recnd
    @22
    cB
    @72
    recnd
    @2
    cB
    cc0
    wne
    @1
    @11
    cB
    rpne0
    ad2antlr
    divcan2d
    adantr
    3eqtrd
    @63
    cr
    @49
    @67
    wf
    #
    @50
    @67
    @9
    cle
    cofr
    wbr
    #
    @68
    @10
    cle
    wbr
    @3
    @73
    @11
    @62
    @3
    vx
    cr
    @66
    @49
    @67
    @3
    @66
    @49
    wcel
    #
    @51
    @3
    @53
    @54
    @75
    @3
    @55
    @17
    @53
    @3
    cB
    @2
    @16
    @1
    @18
    adantl
    #
    rexrd
    @2
    @17
    @1
    @20
    adantl
    #
    @56
    sylanbrc
    0e0iccpnf
    @65
    cB
    cc0
    @49
    ifcl
    sylancl
    adantr
    #
    @67
    eqid
    fmptd
    ad2antrr
    @22
    @50
    @62
    @58
    adantr
    @22
    @3
    @38
    @74
    @62
    @3
    @11
    simpl
    @61
    @38
    @40
    simprl
    @3
    @38
    @66
    @8
    cle
    wbr
    #
    vx
    cr
    wral
    #
    @74
    @3
    @38
    wa
    #
    @79
    vx
    cr
    @81
    @51
    wa
    #
    @65
    @79
    @82
    @65
    wa
    #
    cB
    cB
    @66
    @8
    cle
    @83
    cB
    @3
    @16
    @38
    @51
    @65
    @76
    ad3antrrr
    leidd
    @65
    @66
    cB
    wceq
    @82
    @65
    cB
    cc0
    iftrue
    adantl
    @83
    @7
    cB
    cc0
    @82
    @37
    cA
    @6
    @3
    @38
    @51
    simplr
    sselda
    iftrued
    3brtr4d
    @82
    @65
    wn
    #
    wa
    @66
    cc0
    @8
    cle
    @84
    @66
    cc0
    wceq
    @82
    @65
    cB
    cc0
    iffalse
    adantl
    @3
    cc0
    @8
    cle
    wbr
    #
    @38
    @51
    @84
    @3
    @17
    cc0
    cc0
    cle
    wbr
    #
    @85
    @77
    0le0
    @7
    @17
    @86
    @85
    cB
    cc0
    cB
    @8
    cc0
    cle
    breq2
    cc0
    @8
    cc0
    cle
    breq2
    ifboth
    sylancl
    ad3antrrr
    eqbrtrd
    pm2.61dan
    ralrimiva
    @3
    @74
    @80
    @3
    vx
    cr
    @66
    @8
    cle
    @67
    @9
    cvv
    @49
    @49
    cr
    cvv
    wcel
    @3
    reex
    a1i
    @78
    @57
    @3
    @67
    eqidd
    @3
    @9
    eqidd
    ofrfval2
    biimpar
    syldan
    syl2an
    @67
    @9
    itg2le
    syl3anc
    eqbrtrrd
    @63
    @10
    @25
    clt
    wbr
    #
    @64
    wn
    @11
    @87
    @3
    @62
    @10
    ltp1
    ad2antlr
    @63
    @10
    @25
    @3
    @11
    @62
    simplr
    @11
    @32
    @3
    @62
    @33
    ad2antlr
    ltnled
    mpbid
    pm2.21dd
    rexlimdvaa
    syld
    imp
    @22
    @23
    cxr
    wcel
    @46
    @27
    @29
    wo
    @22
    @4
    @23
    cxr
    @24
    @1
    @59
    @2
    @11
    @60
    ad2antrr
    eqeltrrd
    @22
    @26
    @36
    rexrd
    @23
    @26
    xrletri
    syl2anc
    mpjaodan
    eqeltrd
    impbida
end
