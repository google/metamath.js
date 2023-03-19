include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "cply.mm"
include "cfv.mm"
include "cdgr.mm"
include "wceq.mm"
include "cidp.mm"
include "csn.mm"
include "cxp.mm"
include "cmin.mm"
include "cof.mm"
include "co.mm"
include "cquot.mm"
include "c0p.mm"
include "wne.mm"
include "plyssc.mm"
include "adantr.mm"
include "sseldi.mm"
include "c1.mm"
include "ccnv.mm"
include "cc0.mm"
include "cima.mm"
include "w3a.mm"
include "cdm.mm"
include "cnvimass.mm"
include "eqsstri.mm"
include "wf.mm"
include "plyf.mm"
include "syl.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "sselda.mm"
include "eqid.mm"
include "plyremlem.mm"
include "simp1d.mm"
include "simp2d.mm"
include "ax-1ne0.mm"
include "a1i.mm"
include "eqnetrd.mm"
include "fveq2.mm"
include "dgr0.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "quotcl2.mm"
include "syl3anc.mm"
include "syl5eqel.mm"
include "ax-1cn.mm"
include "nncnd.mm"
include "cn0.mm"
include "dgrcl.mm"
include "nn0cnd.mm"
include "caddc.mm"
include "addcom.mm"
include "sylancr.mm"
include "cmul.mm"
include "eleq2i.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "fniniseg.mm"
include "syl5bb.mm"
include "simplbda.mm"
include "facth.mm"
include "oveq2i.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "wo.mm"
include "wn.mm"
include "cn.mm"
include "peano2nnd.mm"
include "eqeltrrd.mm"
include "nnne0d.mm"
include "syl5eqner.mm"
include "eqnetrrd.mm"
include "plymul0or.mm"
include "syl2anc.mm"
include "necon3abid.mm"
include "mpbid.mm"
include "neanior.mm"
include "sylibr.mm"
include "simprd.mm"
include "dgrmul.mm"
include "syl22anc.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "addcanad.mm"
include "jca.mm"

theorem vieta1lem1
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cF: class F
  let cN: class N
  let vk: setvar k
  let vy: setvar y
  let vd: setvar d
  let vg: setvar g
  assume vieta1.1: |- A = ( coeff ` F )
  assume vieta1.2: |- N = ( deg ` F )
  assume vieta1.3: |- R = ( `' F " { 0 } )
  assume vieta1.4: |- ( ph -> F e. ( Poly ` S ) )
  assume vieta1.5: |- ( ph -> ( # ` R ) = N )
  assume vieta1lem.6: |- ( ph -> D e. NN )
  assume vieta1lem.7: |- ( ph -> ( D + 1 ) = N )
  assume vieta1lem.8: |- ( ph -> A. f e. ( Poly ` CC ) ( ( D = ( deg ` f ) /\ ( # ` ( `' f " { 0 } ) ) = ( deg ` f ) ) -> sum_ x e. ( `' f " { 0 } ) x = -u ( ( ( coeff ` f ) ` ( ( deg ` f ) - 1 ) ) / ( ( coeff ` f ) ` ( deg ` f ) ) ) ) )
  assume vieta1lem.9: |- Q = ( F quot ( Xp oF - ( CC X. { z } ) ) )

  disjoint D f
  disjoint F f
  disjoint f z
  disjoint N f
  disjoint N z
  disjoint f x
  disjoint Q f
  disjoint Q x
  disjoint R f
  disjoint x z
  disjoint R x
  disjoint R z
  disjoint A f
  disjoint A z
  disjoint ph x
  disjoint ph z
  disjoint f k
  disjoint f y
  disjoint k y
  disjoint k z
  disjoint N k
  disjoint y z
  disjoint N y
  disjoint k x
  disjoint Q k
  disjoint d f
  disjoint d g
  disjoint d k
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint R d
  disjoint f g
  disjoint g k
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint R g
  disjoint R k
  disjoint x y
  disjoint R y
  disjoint k ph
  assert |- ( ( ph /\ z e. R ) -> ( Q e. ( Poly ` CC ) /\ D = ( deg ` Q ) ) )

  proof
    wph
    vz
    cv
    #
    cR
    wcel
    #
    wa
    #
    cQ
    cc
    cply
    cfv
    #
    wcel
    #
    cD
    cQ
    cdgr
    cfv
    #
    wceq
    @2
    cQ
    cF
    cidp
    cc
    @0
    csn
    #
    cxp
    cmin
    cof
    co
    #
    cquot
    co
    #
    @3
    vieta1lem.9
    @2
    cF
    @3
    wcel
    @7
    @3
    wcel
    #
    @7
    c0p
    wne
    #
    @8
    @3
    wcel
    @2
    cS
    cply
    cfv
    #
    @3
    cF
    cS
    plyssc
    wph
    cF
    @11
    wcel
    #
    @1
    vieta1.4
    adantr
    #
    sseldi
    @2
    @9
    @7
    cdgr
    cfv
    #
    c1
    wceq
    #
    @7
    ccnv
    cc0
    csn
    #
    cima
    @6
    wceq
    #
    @2
    @0
    cc
    wcel
    #
    @9
    @15
    @17
    w3a
    wph
    cR
    cc
    @0
    wph
    cF
    cdm
    #
    cR
    cc
    cR
    cF
    ccnv
    @16
    cima
    #
    @19
    vieta1.3
    cF
    @16
    cnvimass
    eqsstri
    wph
    cc
    cc
    cF
    wf
    #
    @19
    cc
    wceq
    wph
    @12
    @21
    vieta1.4
    cS
    cF
    plyf
    syl
    #
    cc
    cc
    cF
    fdm
    syl
    syl5sseq
    sselda
    #
    @0
    @7
    @7
    eqid
    #
    plyremlem
    syl
    #
    simp1d
    #
    @2
    @14
    cc0
    wne
    @10
    @2
    @14
    c1
    cc0
    @2
    @9
    @15
    @17
    @25
    simp2d
    #
    c1
    cc0
    wne
    @2
    ax-1ne0
    a1i
    eqnetrd
    @7
    c0p
    @14
    cc0
    @7
    c0p
    wceq
    #
    @14
    c0p
    cdgr
    cfv
    #
    cc0
    @7
    c0p
    cdgr
    fveq2
    dgr0
    syl6eq
    necon3i
    syl
    #
    cc
    cF
    @7
    quotcl2
    syl3anc
    syl5eqel
    #
    @2
    c1
    cD
    @5
    c1
    cc
    wcel
    #
    @2
    ax-1cn
    a1i
    wph
    cD
    cc
    wcel
    #
    @1
    wph
    cD
    vieta1lem.6
    nncnd
    adantr
    #
    @2
    @5
    @2
    @4
    @5
    cn0
    wcel
    @31
    cc
    cQ
    dgrcl
    syl
    nn0cnd
    @2
    c1
    cD
    caddc
    co
    #
    cD
    c1
    caddc
    co
    #
    @14
    @5
    caddc
    co
    #
    c1
    @5
    caddc
    co
    @2
    @32
    @33
    @35
    @36
    wceq
    ax-1cn
    @34
    c1
    cD
    addcom
    sylancr
    @2
    @36
    cF
    cdgr
    cfv
    #
    @7
    cQ
    cmul
    cof
    #
    co
    #
    cdgr
    cfv
    #
    @37
    wph
    @36
    @38
    wceq
    @1
    wph
    @36
    cN
    @38
    vieta1lem.7
    vieta1.2
    syl6eq
    adantr
    @2
    cF
    @40
    cdgr
    @2
    cF
    @7
    @8
    @39
    co
    #
    @40
    @2
    @12
    @18
    @0
    cF
    cfv
    cc0
    wceq
    #
    cF
    @42
    wceq
    @13
    @23
    wph
    @1
    @18
    @43
    @1
    @0
    @20
    wcel
    #
    wph
    @18
    @43
    wa
    #
    cR
    @20
    @0
    vieta1.3
    eleq2i
    wph
    cF
    cc
    wfn
    #
    @44
    @45
    wb
    wph
    @21
    @46
    @22
    cc
    cc
    cF
    ffn
    syl
    cc
    cc0
    @0
    cF
    fniniseg
    syl
    syl5bb
    simplbda
    @0
    cS
    cF
    @7
    @24
    facth
    syl3anc
    cQ
    @8
    @7
    @39
    vieta1lem.9
    oveq2i
    syl6eqr
    #
    fveq2d
    @2
    @9
    @10
    @4
    cQ
    c0p
    wne
    #
    @41
    @37
    wceq
    @26
    @30
    @31
    @2
    @10
    @48
    @2
    @28
    cQ
    c0p
    wceq
    wo
    #
    wn
    #
    @10
    @48
    wa
    @2
    @40
    c0p
    wne
    @50
    @2
    cF
    @40
    c0p
    @47
    wph
    cF
    c0p
    wne
    #
    @1
    wph
    @38
    cc0
    wne
    @51
    wph
    @38
    cN
    cc0
    vieta1.2
    wph
    cN
    wph
    @36
    cN
    cn
    vieta1lem.7
    wph
    cD
    vieta1lem.6
    peano2nnd
    eqeltrrd
    nnne0d
    syl5eqner
    cF
    c0p
    @38
    cc0
    cF
    c0p
    wceq
    @38
    @29
    cc0
    cF
    c0p
    cdgr
    fveq2
    dgr0
    syl6eq
    necon3i
    syl
    adantr
    eqnetrrd
    @2
    @49
    @40
    c0p
    @2
    @9
    @4
    @40
    c0p
    wceq
    @49
    wb
    @26
    @31
    cc
    @7
    cQ
    plymul0or
    syl2anc
    necon3abid
    mpbid
    @7
    c0p
    cQ
    c0p
    neanior
    sylibr
    simprd
    cc
    @7
    cQ
    @14
    @5
    @14
    eqid
    @5
    eqid
    dgrmul
    syl22anc
    3eqtrd
    @2
    @14
    c1
    @5
    caddc
    @27
    oveq1d
    3eqtrd
    addcanad
    jca
end
