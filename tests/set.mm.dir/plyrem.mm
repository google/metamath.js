include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "wa.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cdgr.mm"
include "wceq.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "c0p.mm"
include "wo.mm"
include "wi.mm"
include "wne.mm"
include "plyssc.mm"
include "simpl.mm"
include "sseldi.mm"
include "ccnv.mm"
include "cima.mm"
include "w3a.mm"
include "plyremlem.mm"
include "adantl.mm"
include "simp1d.mm"
include "simp2d.mm"
include "ax-1ne0.mm"
include "a1i.mm"
include "eqnetrd.mm"
include "fveq2.mm"
include "dgr0.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "syl.mm"
include "quotdgr.mm"
include "syl3anc.mm"
include "0lt1.mm"
include "syl5breqr.mm"
include "breq1d.mm"
include "syl5ibrcom.mm"
include "pm2.62.mm"
include "sylc.mm"
include "breqtrd.mm"
include "cn0.mm"
include "wb.mm"
include "cquot.mm"
include "co.mm"
include "cmul.mm"
include "cof.mm"
include "cmin.mm"
include "quotcl2.mm"
include "plymulcl.mm"
include "syl2anc.mm"
include "plysubcl.mm"
include "syl5eqel.mm"
include "dgrcl.mm"
include "nn0lt10b.mm"
include "mpbid.mm"
include "0dgrb.mm"
include "fveq1d.mm"
include "fveq1i.mm"
include "cvv.mm"
include "wf.mm"
include "wfn.mm"
include "plyf.mm"
include "adantr.mm"
include "ffn.mm"
include "cnex.mm"
include "inidm.mm"
include "offn.mm"
include "eqidd.mm"
include "cun.mm"
include "wss.mm"
include "simp3d.mm"
include "ssun1.mm"
include "syl6eqssr.mm"
include "snssg.mm"
include "mpbird.mm"
include "ofmulrt.mm"
include "eleqtrrd.mm"
include "fniniseg.mm"
include "simprd.mm"
include "ofval.mm"
include "anabss3.mm"
include "syl5eq.mm"
include "ffvelrnda.mm"
include "subid1d.mm"
include "eqtrd.mm"
include "fvex.mm"
include "fvconst2.mm"
include "3eqtr3d.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "eqtr4d.mm"

theorem plyrem
  let cA: class A
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let vz: setvar z
  assume plyrem.1: |- G = ( Xp oF - ( CC X. { A } ) )
  assume plyrem.2: |- R = ( F oF - ( G oF x. ( F quot G ) ) )


  assert |- ( ( F e. ( Poly ` S ) /\ A e. CC ) -> R = ( CC X. { ( F ` A ) } ) )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    cA
    cc
    wcel
    #
    wa
    #
    cR
    cc
    cc0
    cR
    cfv
    #
    csn
    #
    cxp
    #
    cc
    cA
    cF
    cfv
    #
    csn
    #
    cxp
    @3
    cR
    cdgr
    cfv
    #
    cc0
    wceq
    #
    cR
    @6
    wceq
    #
    @3
    @9
    c1
    clt
    wbr
    #
    @10
    @3
    @9
    cG
    cdgr
    cfv
    #
    c1
    clt
    @3
    cR
    c0p
    wceq
    #
    @9
    @13
    clt
    wbr
    #
    wo
    #
    @14
    @15
    wi
    @15
    @3
    cF
    cc
    cply
    cfv
    #
    wcel
    #
    cG
    @17
    wcel
    #
    cG
    c0p
    wne
    #
    @16
    @3
    @0
    @17
    cF
    cS
    plyssc
    @1
    @2
    simpl
    sseldi
    #
    @3
    @19
    @13
    c1
    wceq
    #
    cG
    ccnv
    cc0
    csn
    #
    cima
    #
    cA
    csn
    #
    wceq
    #
    @2
    @19
    @22
    @26
    w3a
    @1
    cA
    cG
    plyrem.1
    plyremlem
    adantl
    #
    simp1d
    #
    @3
    @13
    cc0
    wne
    @20
    @3
    @13
    c1
    cc0
    @3
    @19
    @22
    @26
    @27
    simp2d
    #
    c1
    cc0
    wne
    @3
    ax-1ne0
    a1i
    eqnetrd
    cG
    c0p
    @13
    cc0
    cG
    c0p
    wceq
    @13
    c0p
    cdgr
    cfv
    #
    cc0
    cG
    c0p
    cdgr
    fveq2
    dgr0
    syl6eq
    necon3i
    syl
    #
    cR
    cc
    cF
    cG
    plyrem.2
    quotdgr
    syl3anc
    @3
    @15
    @14
    cc0
    @13
    clt
    wbr
    @3
    cc0
    c1
    @13
    clt
    0lt1
    @29
    syl5breqr
    @14
    @9
    cc0
    @13
    clt
    @14
    @9
    @30
    cc0
    cR
    c0p
    cdgr
    fveq2
    dgr0
    syl6eq
    breq1d
    syl5ibrcom
    @14
    @15
    pm2.62
    sylc
    @29
    breqtrd
    @3
    @9
    cn0
    wcel
    #
    @12
    @10
    wb
    @3
    cR
    @17
    wcel
    #
    @32
    @3
    cR
    cF
    cG
    cF
    cG
    cquot
    co
    #
    cmul
    cof
    co
    #
    cmin
    cof
    co
    #
    @17
    plyrem.2
    @3
    @18
    @35
    @17
    wcel
    #
    @36
    @17
    wcel
    @21
    @3
    @19
    @34
    @17
    wcel
    #
    @37
    @28
    @3
    @18
    @19
    @20
    @38
    @21
    @28
    @31
    cc
    cF
    cG
    quotcl2
    syl3anc
    #
    cc
    cG
    @34
    plymulcl
    syl2anc
    cc
    cF
    @35
    plysubcl
    syl2anc
    syl5eqel
    #
    cc
    cR
    dgrcl
    syl
    @9
    nn0lt10b
    syl
    mpbid
    @3
    @33
    @10
    @11
    wb
    @40
    cc
    cR
    0dgrb
    syl
    mpbid
    #
    @3
    @8
    @5
    cc
    @3
    @7
    @4
    @3
    cA
    cR
    cfv
    #
    cA
    @6
    cfv
    #
    @7
    @4
    @3
    cA
    cR
    @6
    @41
    fveq1d
    @3
    @42
    @7
    cc0
    cmin
    co
    #
    @7
    @3
    @42
    cA
    @36
    cfv
    #
    @44
    cA
    cR
    @36
    plyrem.2
    fveq1i
    @1
    @2
    @45
    @44
    wceq
    @3
    cc
    cc
    @7
    cc0
    cmin
    cc
    cF
    @35
    cvv
    cvv
    cA
    @3
    cc
    cc
    cF
    wf
    #
    cF
    cc
    wfn
    @1
    @46
    @2
    cS
    cF
    plyf
    #
    adantr
    cc
    cc
    cF
    ffn
    syl
    @3
    cc
    cc
    cmul
    cc
    cG
    @34
    cvv
    cvv
    @3
    cc
    cc
    cG
    wf
    #
    cG
    cc
    wfn
    @3
    @19
    @48
    @28
    cc
    cG
    plyf
    syl
    #
    cc
    cc
    cG
    ffn
    syl
    @3
    cc
    cc
    @34
    wf
    #
    @34
    cc
    wfn
    @3
    @38
    @50
    @39
    cc
    @34
    plyf
    syl
    #
    cc
    cc
    @34
    ffn
    syl
    cc
    cvv
    wcel
    #
    @3
    cnex
    a1i
    #
    @53
    cc
    inidm
    #
    offn
    #
    @53
    @53
    @54
    @3
    @2
    wa
    @7
    eqidd
    @3
    cA
    @35
    cfv
    cc0
    wceq
    #
    @2
    @3
    @2
    @56
    @3
    cA
    @35
    ccnv
    @23
    cima
    #
    wcel
    #
    @2
    @56
    wa
    #
    @3
    cA
    @24
    @34
    ccnv
    @23
    cima
    #
    cun
    #
    @57
    @3
    cA
    @61
    wcel
    #
    @25
    @61
    wss
    #
    @3
    @25
    @24
    @61
    @3
    @19
    @22
    @26
    @27
    simp3d
    @24
    @60
    ssun1
    syl6eqssr
    @2
    @62
    @63
    wb
    @1
    cA
    @61
    cc
    snssg
    adantl
    mpbird
    @3
    @52
    @48
    @50
    @57
    @61
    wceq
    @53
    @49
    @51
    cc
    cG
    @34
    cvv
    ofmulrt
    syl3anc
    eleqtrrd
    @3
    @35
    cc
    wfn
    @58
    @59
    wb
    @55
    cc
    cc0
    cA
    @35
    fniniseg
    syl
    mpbid
    simprd
    adantr
    ofval
    anabss3
    syl5eq
    @3
    @7
    @1
    cc
    cc
    cA
    cF
    @47
    ffvelrnda
    subid1d
    eqtrd
    @2
    @43
    @4
    wceq
    @1
    cc
    @4
    cA
    cc0
    cR
    fvex
    fvconst2
    adantl
    3eqtr3d
    sneqd
    xpeq2d
    eqtr4d
end
